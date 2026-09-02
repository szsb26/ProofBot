"""
Lean 4 REPL subprocess wrapper.

Manages a long-running `lake exe repl` process, communicating via JSON
over stdin/stdout. Implements the LeanExecutor protocol.

Protocol (discovered via testing):
    - Launch:  lake exe repl from lean_project directory
    - Send:    json.dumps(payload) + "\\n\\n"  (blank line terminator)
    - Read:    lines until blank line, join, parse as JSON

    Initialize proof:
        send: {"cmd": "theorem ... := by\\n  sorry"}
        recv: {"sorries": [{"proofState": 0, "goal": "⊢ ..."}], "env": 0}

    Apply tactic:
        send: {"tactic": "simp", "proofState": 0}
        recv: {"proofState": 1, "goals": ["n : Nat\\n⊢ n + 0 = n"]}  # incomplete
        recv: {"proofState": 2, "goals": [], "proofStatus": "Completed"}  # done
        recv: {"message": "Lean error:\\n..."}  # failed

    Branching:
        Send two different tactics with the same proofState N.
        Each gets an independent new proofState number.
        This is how we explore multiple branches without restarting Lean.

Compute hierarchy (one SubprocessExecutor = one search worker):

SubprocessExecutor  (thin Python coordinator, one per LedgerSearch instance)
│
└── LeanWorker  (one lake exe repl OS subprocess, unique PID and memory)
    │
    │  owns:
    │  ├── _proc: asyncio.subprocess.Process   ← one lake exe repl OS process
    │  └── _proof_state_cache: dict[str, int]  ← stable_hash → REPL integer ID
    │
    └── lake exe repl  (one OS process)
        │
        │  owns (internal to Lean, not visible to Python):
        │  ├── loaded Mathlib environment
        │  └── proof state table: { 0: <state>, 1: <state>, 2: <state>, ... }

For k parallel proof searches, create k SubprocessExecutor instances and run
k LedgerSearch.prove() coroutines concurrently with asyncio.gather().
Each executor owns exactly one worker process, so there is no cross-worker
routing or session tracking needed.
"""

from __future__ import annotations

import asyncio
import json
import logging
import os
import re
import time
from pathlib import Path
from typing import Optional

from core.executor import LeanExecutor, StepResult
from core.proof_state import Goal, ProofState

logger = logging.getLogger(__name__)

# Path to the lean_project directory — where lake exe repl is run from
# Think of a lean project as something that is similar to a python virtual environment -
# it contains the Lean files, dependencies, and compiled artifacts needed to run the REPL.
LEAN_PROJECT_DIR = Path(__file__).parent.parent / "lean_project"

# Raised as a ProofState.error when a state cannot be reached because the REPL
# subprocess was restarted and could not be rebuilt. Distinct from a Lean error
# because it says nothing about the mathematics — the search should end the
# trial rather than keep spending budget.
WORKER_LOST_ERROR = "Lean worker was restarted and this proof state could not be rebuilt"

_BY_KEYWORD_RE = re.compile(r"\bby\b")
# Matches a top-level segment ending in "have NAME : STMT :=" (or the
# anonymous "have : STMT :="), right before its inline proof's "by" —
# the shape auto-split into a bare sub-goal, see _split_top_level_tactics.
# Requires an explicit type annotation (a ':' not immediately
# followed by '=') between "have" and the trailing ":=" — "have h :=
# by simp" has no separately-stated type, so there is nothing valid to
# open as a bare sub-goal; its type only exists once the proof does.
# Confirmed against a real Lean REPL: bare "have h" with no type at
# all is rejected outright.
_HAVE_WITH_INLINE_PROOF_RE = re.compile(r"^have\b(\s+\S+)?\s*:(?!=).*:=$", re.DOTALL)
# A top-level "=>" opens a body whose ';' sequence that body rather than
# separating steps — "induction x with | a => …", "case pos => …",
# "next => …", "conv => …". The one construct where "=>" does NOT open such a
# body is a lambda ("exact fun x => x; simp"), so that is the exception tested
# for, rather than enumerating the keywords that do.
_LAMBDA_KEYWORD_RE = re.compile(r"(?:\bfun\b|λ)")
# Bracket pairs that must suppress splitting. Anonymous-constructor brackets
# ⟨⟩ are included: without them a "by" inside ⟨…⟩ reads as top-level and
# aborts the scan, shipping an unsplit ';' that Lean rejects outright.
_OPEN_BRACKETS = "([{⟨"
_CLOSE_BRACKETS = ")]}⟩"
# Lean's focus dot. A "· tac; tac" block is one tactic whose body runs on the
# focused goal and must close it, so its ';' are not step separators.
_FOCUS_DOT = "·"

# Lean prefixes syntax errors with the source position it choked at
# ("<input>:1:7: expected end of input"). Elaboration errors — unknown
# constant, type mismatch, unsolved goals — carry no such prefix, so this
# distinguishes "you sent me something I cannot parse" from "I ran it and it
# failed".
_PARSE_ERROR_RE = re.compile(r"<input>:\d+:\d+:")


def _is_parse_error(response: dict) -> bool:
    """True when Lean rejected the string as syntax rather than running it."""
    blob = str(response.get("message", ""))
    for m in response.get("messages") or []:
        blob += " " + str(m.get("data", ""))
    return bool(_PARSE_ERROR_RE.search(blob))


def _has_error_messages(response: dict) -> bool:
    """True when Lean returned a state but logged an error alongside it."""
    return any(
        m.get("severity") == "error" for m in (response.get("messages") or [])
    )


def _is_have_decomposition(tactic: str, parts: list[str]) -> bool:
    """
    Did the splitter open a bare sub-goal from "have NAME : STMT := by REST"?

    That split is deliberate rather than a parsing workaround — it exists to
    checkpoint the sub-proof step by step (see _split_top_level_tactics) — and
    the original string parses whole, so the preflight in `step` would
    otherwise silently undo it.
    """
    stripped = tactic.strip()
    head = parts[0].strip()
    if not head.startswith("have") or not stripped.startswith(head):
        return False
    return stripped[len(head):].lstrip().startswith(":=")


def _candidate_boundaries(tactic: str) -> list[int]:
    """Offsets of every ';' that COULD be a step separator.

    Bracket depth is lexical and unambiguous, so this is a superset of the
    real cut points — deliberately including the ones _split_top_level_tactics
    protects (branch bodies, focus blocks, `with |` alternatives). Which of
    them is real is decided by Lean in `_discover_steps`, not by us: every
    time we have decided that ourselves we have eventually been wrong.

    Only '<;>' is excluded, because splitting there corrupts the token itself
    into two invalid fragments rather than producing a wrong-but-valid split.
    """
    out: list[int] = []
    depth = 0
    n = len(tactic)
    for i, c in enumerate(tactic):
        if c in _OPEN_BRACKETS:
            depth += 1
        elif c in _CLOSE_BRACKETS:
            depth = max(depth - 1, 0)
        elif depth == 0 and c == ";":
            if i > 0 and i + 1 < n and tactic[i - 1] == "<" and tactic[i + 1] == ">":
                continue
            out.append(i)
    return out


def _peel_bare_have(tactic: str) -> Optional[tuple[str, str]]:
    """Split "have NAME : STMT := by REST" into ("have NAME : STMT", REST).

    The one decomposition that is deliberate rather than a parsing workaround:
    the whole string parses fine, so Lean would happily run it as one atomic
    unit — and that is exactly the problem. Measured on tournament_champion,
    347 inlined sub-lemmas were proposed and every sampled failure was a small
    mechanical slip *inside* the `by` block, discarding a correct decomposition
    each time. Opening the bare `have` instead keeps the sub-goal attackable
    step by step. Returns None when the tactic is not that shape.
    """
    parts = _split_top_level_tactics(tactic)
    # Not `len(parts) < 2`: "have h : T := by" with an empty body splits to a
    # single part, and that is exactly the shape worth peeling.
    if not parts or not _is_have_decomposition(tactic, parts):
        return None
    head = parts[0].strip()
    rest = tactic.strip()[len(head):].lstrip()
    if not rest.startswith(":="):
        return None
    rest = rest[2:].lstrip()
    if _BY_KEYWORD_RE.match(rest, 0):
        rest = rest[2:].lstrip()
    # An empty REST ("have h : T := by" with nothing after it) still peels.
    # Lean rejects that string outright — an empty `by` block is a syntax
    # error — so sending it whole costs a turn for nothing, while the bare
    # `have` is plainly what was intended and opens the sub-goal. 22 recorded
    # tactics have this shape.
    return head, rest


def _split_top_level_tactics(tactic: str) -> list[str]:
    """
    Split a tactic string on top-level ';' into individual Lean 4 tactics.

    The REPL's tactic-stepping endpoint (`{"tactic": ..., "proofState": ...}`)
    only parses one atomic `tactic` per call, not a `tacticSeq` — confirmed
    empirically: even a trivially valid "t1; t2" is rejected outright with
    "expected end of input" right after t1, regardless of whether t2 is
    separated by ';' or by a newline. Splitting on our end and sending each
    step as its own sequential call lets a chained candidate actually run
    instead of being silently lost to a parse error.

    Three kinds of ';' are NOT separators and must be left alone, because in
    each the semicolon sequences tactics *inside* a construct that Lean
    parses as one atomic tactic:

      * inside an alternative body of a structured tactic —
        "induction xs with | nil => intro a; simp | cons hd tl ih => ...".
        Splitting ships a truncated alternative list, and Lean answers
        "unsolved goals" for the branches that never arrived. The model sees
        only that the step failed, so it rewrites a branch that never ran:
        imo2026_q3_spec_share_bounds sent "induction xs with | nil => intro a"
        thirteen times running (raw log seq 339-351) across 14 turns and
        eleven different branch bodies, none of which reached Lean; imo2026_q6
        lost its last four turns the same way. 51 of 576 tactics in one
        evaluation were truncated like this.
      * inside a focus block — "· simp; omega". The dot requires its body to
        close the focused goal, so "· simp" alone fails whenever `simp` does
        not finish the job.
      * inside ⟨⟩ — anonymous-constructor brackets count toward depth, so a
        "by" in "refine ⟨x, by linarith, ?_⟩; rest" no longer aborts the scan
        and leaves the top-level ';' in the string for Lean to reject.

    Confirmed against a real Lean REPL: the tactic endpoint accepts
    "induction n with | zero => rfl | succ k ih => rw [Nat.succ_add]; rw [ih]"
    and "· rw [Nat.add_comm]; rfl" as single tactics, while "intro h; exact h"
    is still rejected outright — so plain chains must still be split.

    Semicolons that are part of Lean's '<;>' combinator ("run this tactic
    on every goal produced by the previous one") are also left untouched —
    splitting there corrupts the token into two dangling fragments (e.g.
    "cases h1 <;> cases h2" becomes "cases h1 <" and "> cases h2", both
    invalid syntax). Confirmed as a real, previously-uncaught bug: a live
    trace showed every candidate using '<;>' failing with a syntax error
    at exactly that point, for every model, until one caught it and
    rewrote around it with 'all_goals' instead.

    Semicolons inside brackets, or anywhere after a top-level 'by' (a
    reserved keyword, so an unbracketed occurrence unambiguously opens a
    nested tacticSeq — e.g. "have h := by t1; t2"), are left untouched: in
    a flat, unindented one-line string there's no dedent boundary to close
    that block early, so everything to the right of 'by' belongs to it and
    must be sent to Lean as a single unit — WITH ONE EXCEPTION:

    "have NAME : STMT := by REST" is special-cased. Sending it whole makes
    the sub-goal's entire proof pass or fail atomically, discarding a
    correct decomposition whenever anything inside REST goes wrong — the
    single largest measured cause of tournament_champion's failures (347
    inlined sub-lemmas proposed, every sampled one failing inside `by`).
    Confirmed against a real Lean REPL: sending the bare "have NAME : STMT"
    alone (no proof) opens STMT as a new first goal and keeps the original
    goal available with NAME as a hypothesis — and Lean's default "operate
    on the first goal" behavior then routes REST's own steps onto that new
    sub-goal with no extra bookkeeping needed. So instead of shipping
    "have NAME : STMT := by REST" as one block, this yields the bare
    "have NAME : STMT" as its own step, then recurses on REST — meaning a
    nested "have ... := by ..." inside REST gets split again the same way,
    fully unrolling any depth of nesting into a flat sequence of
    individually-checkpointed steps.
    """
    parts: list[str] = []
    depth = 0
    start = 0
    i = 0
    n = len(tactic)
    # Set once a top-level '·' has been seen: everything after it belongs to
    # that focus block until the next top-level '·'.
    in_focus_block = False
    while i < n:
        c = tactic[i]
        if c in _OPEN_BRACKETS:
            depth += 1
        elif c in _CLOSE_BRACKETS:
            depth = max(depth - 1, 0)
        elif depth == 0:
            if c == _FOCUS_DOT:
                # A new focus block starts here. Close whatever came before
                # it, then stop treating ';' as a separator until the next
                # dot: "· simp; omega" must reach Lean whole, or the dot
                # demands `simp` alone close the goal and the step fails.
                # A ';' immediately before the next dot separated the two
                # blocks rather than sequencing anything, so it is dropped:
                # "· sorry; · sorry" must not yield a dangling "· sorry;".
                segment = tactic[start:i].strip().rstrip(";").strip()
                if segment:
                    parts.append(segment)
                    start = i
                in_focus_block = True
            elif in_focus_block:
                # Inside a focus block: only another top-level dot ends it.
                pass
            elif tactic.startswith("=>", i) and not _LAMBDA_KEYWORD_RE.search(
                tactic, start, i
            ):
                # This "=>" opens a body — a structured-tactic alternative
                # ("induction x with | nil => intro a; simp | cons …"), a
                # "case pos => …", a "next => …" or a "conv => …". Every ';'
                # from here on sequences that body, so the whole remainder
                # must reach Lean as one tactic. Splitting here shipped a
                # truncated construct that Lean rejected with "unsolved
                # goals", and the model — told only that the step failed —
                # spent up to 14 consecutive turns rewriting a branch that
                # had never run.
                #
                # A lambda's "=>" opens no such body ("exact fun x => x;
                # simp" really is two steps), so a "fun"/"λ" earlier in the
                # current segment suppresses the stop.
                break
            elif c == ";" and i > 0 and i + 1 < n and tactic[i - 1] == "<" and tactic[i + 1] == ">":
                # Part of Lean's '<;>' combinator ("apply to every resulting
                # goal"), not a step separator — splitting here corrupts it
                # into two dangling fragments (e.g. "cases h1 <" / "> ...").
                i += 1
            elif c == ";":
                parts.append(tactic[start:i].strip())
                start = i + 1
            elif _BY_KEYWORD_RE.match(tactic, i):
                segment = tactic[start:i].strip()
                if segment.endswith(":=") and _HAVE_WITH_INLINE_PROOF_RE.match(segment):
                    parts.append(segment[:-2].strip())
                    parts.extend(_split_top_level_tactics(tactic[i + 2:]))
                    return [p for p in parts if p]
                break
        i += 1
    parts.append(tactic[start:].strip())
    return [p for p in parts if p]


def _annotate_chain_error(raw_error: str, sub_tactics: list[str], failed_idx: int) -> str:
    """
    Prefix a Lean error with which step of a multi-step chain caused it.

    A no-op (returns raw_error unchanged) when the candidate wasn't split
    into multiple steps, so single-tactic candidates are unaffected.

    Deliberately reports "step N" and not "step N of M": since Lean decides
    the step boundaries as execution proceeds (see _discover_steps), the
    total is only known once the chain finishes, and a chain that fails
    stops early. Reporting "step 2 of 2" for a three-piece candidate that
    failed on its second step would tell the model its third piece ran.
    """
    if len(sub_tactics) <= 1:
        return raw_error
    body = raw_error
    if body.startswith("Lean error:\n"):
        body = body[len("Lean error:\n"):]
    prefix = "; ".join(sub_tactics[:failed_idx])
    header = f'Lean error (step {failed_idx + 1} in this chain — "{sub_tactics[failed_idx]}" — failed'
    if prefix:
        header += f', after "{prefix}" succeeded'
    header += "):\n"
    return header + body


class LeanREPLError(Exception):
    """Raised when the REPL process dies or returns unexpected output."""
    pass


class LeanWorker:
    """
    A single Lean REPL worker process.

    Wraps one `lake exe repl` subprocess. Manages the proof state cache
    that maps ProofState hashes to REPL proofState numbers.

    Not thread-safe — use one worker per asyncio task, or protect with
    a semaphore (which SubprocessExecutor does via its worker pool).

    Each LeanWorker is a completely separate "lake exe repl" OS subprocess, and
    there is no shared memory between lean workers.

    Because LeanWorker methods are async, we see that SubprocessExecutor methods are also async.
    Recall that async functions are functions that can be paused and resumed, allowing other code to run while waiting for long-running operations.
    In our case, the long-running operations are the interactions with the REPL subprocess, which involve I/O and can take some time to complete.
    By making these methods async, we can ensure that our Python event loop remains responsive and can handle multiple proof attempts in parallel
    without blocking on any single REPL interaction.
    """

    def __init__(
        self,
        lean_project_dir: Path,
        load_mathlib: bool = True,
        raw_log_path: Optional[Path] = None,
    ):
        self._dir = lean_project_dir
        self._proc: Optional[asyncio.subprocess.Process] = None
        self._proof_state_cache: dict[str, int] = {}
        self._load_mathlib = load_mathlib
        # env number returned by "import LeanProject"; 0 if not loaded
        self._base_env: int = 0
        # Optional JSONL log of every REPL exchange (see _log_exchange).
        self._raw_log_path = raw_log_path
        self._raw_log_seq = 0
        # Last theorem/preamble handed to reset(), so a state can be re-derived
        # if the subprocess is restarted mid-search (see _rebuild_state).
        self._last_theorem: str | None = None
        self._last_preamble: str = ""
        self._rebuilding = False

    def _log_exchange(
        self,
        payload: dict,
        response: dict | None,
        elapsed_ms: float,
        error: str | None = None,
    ) -> None:
        """
        Append one REPL exchange to the raw JSONL log, if one is configured.

        This is the ONLY place the unabridged Lean conversation is recorded.
        Everything downstream is lossy in ways that matter when diagnosing a
        failed run:

          - repl.py surfaces `msg_errors[0]` and drops any further errors in
            the same response;
          - the Ledger keeps one error string per attempt, not the response;
          - traces/ record `serialize_ledger` output, i.e. the *prompt*, which
            caps tactic lists at 15 per state (measured: 2807 lists capped
            across our traces, one hiding 672 attempts) and errors at 2000
            chars.

        So a question like "what did Lean actually say" was previously
        unanswerable after the fact. Written per exchange and flushed rather
        than buffered to the end of the trial, so a run that dies partway —
        crash, timeout, exhausted API credits — keeps everything up to the
        failure.
        """
        if not self._raw_log_path:
            return
        self._raw_log_seq += 1
        record = {
            "seq": self._raw_log_seq,
            "ts": time.time(),
            "elapsed_ms": round(elapsed_ms, 2),
            "request": payload,
            "response": response,
        }
        if error is not None:
            record["error"] = error
        try:
            with open(self._raw_log_path, "a") as fh:
                fh.write(json.dumps(record, ensure_ascii=False) + "\n")
        except Exception:
            # Logging must never take down a search.
            logger.warning("failed to append to raw Lean log", exc_info=True)

    async def start(self) -> None:
        """Launch the lake exe repl subprocess.

        worker.start(): launches the Lean subprocess using asyncio.create_subprocess_exec() and sets up the REPL.
        In the mock, we just need it to be an async function that does nothing, since we won't actually start a real REPL. asyncio.create_subprocess_exec()
        itself is an async operation - it asks the OS to spawn a new process, which takes a small amount of time. While the OS is doing that, other coroutines can run.
        So start() must be async because it "awaits" the subprocess creation.

        "lake exe repl" acts exactly like typing "python" in a terminal, and acts as an interactive REPL. All inputs must be in JSON format separated by a blank line. For ex.,

        $ lake exe repl
        {"cmd": "#check Nat.add_zero"}

        {"messages": [...], "env": 0}

        {"tactic": "intro n", "proofState": 0}

        {"proofState": 1, "goals": [...]}

        Also, a process is a running instance of a program. When the process is launched, it has its own memory space, file handles, and system resources.
        In our case, each LeanWorker launches its own "lake exe repl" process, which means each worker has its own separate instance of the Lean REPL running
        in parallel. This allows us to explore multiple branches of the proof tree simultaneously without interference,
        since each REPL process maintains its own proof state table and environment.

        """
        # start the lean REPL subprocess.
        # limit raised well past asyncio's 64KB default: apply?/exact? can
        # emit dozens of verbose "Try this" info messages in one response,
        # producing single lines that exceed the default and crash readline
        # with "Separator is found, but chunk is longer than limit".
        self._proc = await asyncio.create_subprocess_exec(
            "lake", "exe", "repl",
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL,
            cwd=str(self._dir),
            limit=10 * 1024 * 1024,
        )
        logger.debug(f"Started Lean worker pid={self._proc.pid}")

        if self._load_mathlib:
            # Load the compiled project (imports Mathlib) so that tactics like
            # ring, linarith, norm_num etc. are available. Uses pre-built .olean
            # files from `lake build` — slow (~300s) but paid once per process.
            logger.debug("Importing LeanProject (loading Mathlib from .olean files)...")
            response = await self._send({"cmd": "import LeanProject"}, timeout=720.0)
            errors = [m for m in response.get("messages", []) if m.get("severity") == "error"]
            if errors:
                raise LeanREPLError(
                    f"Failed to import LeanProject: {errors[0].get('data', 'unknown error')}"
                )
            self._base_env = response.get("env", 0)
            logger.debug(f"LeanProject loaded in env {self._base_env}")

    async def stop(self) -> None:
        """Terminate the subprocess cleanly.
        
        worker.stop(): stop() waits for the subprocess to terminate cleanly. self._proc.wait() blocks until the Lean process actually exits.
    That could take a moment - Lean needs to flush its output and shut down. Rather than freezing python while waiting, "await" lets other things run in the meantime.
        
        """
        if self._proc and self._proc.returncode is None:
            try:
                self._proc.stdin.close()
                await asyncio.wait_for(self._proc.wait(), timeout=5.0)
            except asyncio.TimeoutError:
                self._proc.kill()
                await self._proc.wait()
        logger.debug("Lean worker stopped")

    async def _drain_stale_response(self, drain_timeout: float = 120.0) -> None:
        """Read and discard REPL stdout until a blank-line separator.

        Called after a _send timeout to consume the response that Lean will
        eventually write, so the next _send reads its own response instead.
        Raises asyncio.TimeoutError if Lean doesn't respond within drain_timeout.
        """
        deadline = time.perf_counter() + drain_timeout
        while True:
            remaining = deadline - time.perf_counter()
            if remaining <= 0:
                raise asyncio.TimeoutError()
            line = await asyncio.wait_for(
                self._proc.stdout.readline(),
                timeout=remaining,
            )
            if line.decode().strip() == "":
                return  # blank line = end of response

    async def _send(self, payload: dict, timeout: float = 30.0) -> dict:
        """
        Send a JSON payload to the REPL and read the response. Every command is terminated with \\n\\n (blank line).
        Every response is terminated with a blank line. _send() in LeanWorker.step(), where we send a tactic(part of the payload)
        to the REPL on the worker and wait for the response.

        As an example of how async and await works, when Python gets to "await self._proc.stdin.drain()", it sends the command to the REPL
        and then pauses the current coroutine, allowing other coroutines to run while waiting for the REPL to respond. Once the REPL responds
        and the command is fully sent, the coroutine resumes and continues to read the response from the REPL.
        This allows us to handle multiple proof attempts in parallel without blocking on any single REPL interaction.

        The await points are exactly where Python steps aside and lets the OS and the Lean process do their work. Lean can take hundreds of milliseconds
        to verify a tactic, and during that time, other workers can continue to run and interact with their
        own REPL proceses.
        """
        # sanity check. We should have used LeanWorker.start() to launch the REPL before calling _send()
        if not self._proc or self._proc.returncode is not None:
            raise LeanREPLError("Lean worker process is not running")

        _send_started = time.perf_counter()

        # .encode() converts the string to bytes, which is what the subprocess stdin expects. json.dumps() converts the payload dictionary
        # to a JSON-formatted string. We add the blank line terminator "\n\n" as required by the REPL protocol.
        msg = (json.dumps(payload) + "\n\n").encode()
        # note that we do not need to use any lean specific python libraries to interact with the REPL.
        # Think of "lake exe repl" as a compiled Lean binary that runs as an interactive process.
        # It: 1) starts up, loads Mathlib into memory, 2)and then sits there waiting for JSON commands on stdin,
        #.    3) responds with JSON on stdout. We can interact with it using standard python subprocess communication patterns
        self._proc.stdin.write(msg)
        # drain() waits until the write buffer is flushed, meaning that the message has actually been sent to the REPL process.
        # This is important because we ensure that the command is fully sent before we start waiting for the response.
        await self._proc.stdin.drain()

        # Read lines until we hit a blank line
        lines = []
        while True:
            try:
                line = await asyncio.wait_for(
                    self._proc.stdout.readline(),
                    timeout=timeout,
                )
            except asyncio.TimeoutError:
                # Lean is still computing. Drain its eventual response so the
                # next _send reads its own response rather than this stale one.
                logger.warning("Lean REPL timed out; draining stale response to prevent desync")
                try:
                    await self._drain_stale_response(drain_timeout=120.0)
                except asyncio.TimeoutError:
                    # Lean appears stuck; kill the subprocess so future calls fail fast
                    # and SubprocessExecutor.reset() can restart it cleanly.
                    logger.error("Lean REPL drain timed out; killing subprocess")
                    try:
                        self._proc.kill()
                        await asyncio.wait_for(self._proc.wait(), timeout=5.0)
                    except Exception:
                        pass
                    self._proof_state_cache.clear()
                # Log the timeout itself: a tactic that never returned is
                # invisible everywhere downstream (no Ledger entry, no prompt
                # text), so without this the raw log would silently skip it.
                self._log_exchange(
                    payload, None,
                    (time.perf_counter() - _send_started) * 1000,
                    error="timeout",
                )
                raise LeanREPLError(
                    f"Lean REPL timed out waiting for response to: {payload}"
                )
            decoded = line.decode()
            if decoded.strip() == "":
                break
            lines.append(decoded)

        elapsed_ms = (time.perf_counter() - _send_started) * 1000

        if not lines:
            self._log_exchange(payload, None, elapsed_ms, error="empty_response")
            raise LeanREPLError("Lean REPL returned empty response")

        raw = "".join(lines)
        try:
            result = json.loads(raw)
        except json.JSONDecodeError:
            self._log_exchange(
                payload, {"_unparsed_stdout": raw[:8000]}, elapsed_ms,
                error="json_decode_error",
            )
            raise
        self._log_exchange(payload, result, elapsed_ms)
        return result

    async def reset(self, theorem: str, preamble: str = "") -> tuple[ProofState, int]:
        """
        Initialize a new proof attempt.

        Sends the theorem with a sorry placeholder to get the initial
        proof state. Returns (ProofState, repl_proof_state_id).
        Note that "sorry" is a special Lean placeholder that creates an open goal,
        allowing us to extract the initial proof state without needing a complete proof. 
        It allows us to get the initial goal state without proving the theorem, which is perfect for our search loop.
        We will replace "sorry" with actual tactics as we explore the proof tree.
        The REPL returns this initial state along with a unique proofState id that we cache
        for future tactic applications. Think of "sorry" as a "TODO" in Lean.

        worker.reset(): In general reset() sends the theorem statement to the REPL and waits for the initial proof state. This involves multiple async steps:
        1. Send the theorem statement to the REPL (async because it writes to the subprocess stdin).
        2. Wait for the REPL to respond with the initial proof state (async because it reads from the subprocess stdout).

        Args:
            theorem: A complete Lean 4 theorem statement ending with := by

        Returns:
            (initial_proof_state, repl_proof_state_id)
        """
        # The proofState cache maps a goal hash to a REPL proofState id, and
        # stable_hash covers only the goal TEXT — not the environment it was
        # elaborated in. That is sound while every problem shares _base_env,
        # but a statement with its own preamble gets its own environment
        # below, and two problems can render an identical goal ("⊢ False"
        # after by_contra is common) while meaning different things in them.
        # Reusing a cached id across that boundary would silently run tactics
        # against the wrong problem's context, so drop it at each reset.
        # Nothing is lost: a finished problem's states are never revisited.
        self._proof_state_cache.clear()
        if not self._rebuilding:
            self._last_theorem, self._last_preamble = theorem, preamble

        # `preamble` holds definitions the statement depends on. They must be
        # committed as their OWN command: a proofState does not carry
        # declarations made in the same command as the theorem, so otherwise
        # every tactic naming one fails with "Unknown identifier" — including
        # `exact h`, since elaborating the existing context needs the names.
        # What counts as a preamble is the problem set's business, not this
        # layer's (see EvalProblem.statement_preamble).

        # Format: "theorem foo : <stmt> := by\n  sorry"
        if ":= by" not in theorem:
            theorem = theorem.rstrip() + " := by"
        cmd = theorem + "\n  sorry"

        # Pass "env" only when Mathlib was loaded. After "import LeanProject",
        # the REPL assigns env 0 to the Mathlib environment. We must pass
        # "env": 0 explicitly so the theorem is elaborated there; without it
        # the REPL uses a fresh blank context where ring/linarith are unavailable.
        # For load_mathlib=False we omit "env" entirely — a fresh REPL has no
        # saved envs yet and passing "env": 0 causes "Unknown environment.".
        env = self._base_env if self._load_mathlib else None

        if preamble:
            pre_payload: dict = {"cmd": preamble}
            if env is not None:
                pre_payload["env"] = env
            pre_resp = await self._send(pre_payload)
            pre_errs = [
                m for m in pre_resp.get("messages", [])
                if m.get("severity") == "error"
            ]
            if "message" in pre_resp or pre_errs:
                # The vocabulary itself failed to elaborate — the theorem
                # cannot mean anything, so report it rather than pressing on
                # and blaming the prover for the fallout.
                why = pre_resp.get("message") or pre_errs[0].get("data", "Lean error")
                return ProofState(goals=(), error=f"statement preamble failed:\n{why}"), -1
            # Elaborate the theorem in the environment the preamble produced.
            env = pre_resp.get("env", env)

        payload: dict = {"cmd": cmd}
        if env is not None:
            payload["env"] = env
        response = await self._send(payload)

        # Check for parse errors
        if "message" in response and "sorries" not in response:
            error_msg = response.get("message", "Unknown error")
            error_state = ProofState(goals=(), error=error_msg)
            return error_state, -1

        # Check for Lean errors in messages
        messages = response.get("messages", [])
        errors = [m for m in messages if m.get("severity") == "error"]
        if errors:
            error_msg = errors[0].get("data", "Lean error")
            error_state = ProofState(goals=(), error=error_msg)
            return error_state, -1

        # Extract proof state from sorries
        sorries = response.get("sorries", [])
        if not sorries:
            # No sorries means theorem was proved trivially
            closed_state = ProofState(goals=())
            return closed_state, -1

        sorry = sorries[0]
        repl_ps_id = sorry["proofState"]
        goal_str = sorry.get("goal", "")

        # Lean's own words, carried verbatim — no reconstruction.
        initial_state = (
            ProofState(goals=(Goal(text=goal_str.strip()),))
            if goal_str.strip() else ProofState(goals=())
        )

        # Cache this proof state
        self._proof_state_cache[initial_state.stable_hash()] = repl_ps_id

        return initial_state, repl_ps_id

    async def _rebuild_state(self, state: ProofState) -> Optional[int]:
        """Re-derive a proof state after the worker was restarted.

        Replays the state's tactic_trace from a fresh reset. Costs one REPL
        call per tactic in the path, which is far cheaper than losing the rest
        of the search — the alternative, measured, was 41 dead turns out of 49.

        Returns the new REPL proofState id, or None if recovery is impossible
        (no theorem recorded yet, reset fails, or a replayed tactic no longer
        lands where it did — e.g. it was nondeterministic).
        """
        if self._last_theorem is None or self._rebuilding:
            return None
        self._rebuilding = True
        try:
            logger.warning(
                "rebuilding proof state after worker restart (replaying %d tactic(s))",
                len(state.tactic_trace),
            )
            base, _ = await self.reset(self._last_theorem, self._last_preamble)
            if base.is_error:
                return None
            current = base
            for tac in state.tactic_trace:
                result = await self.step(current, tac)
                if result.next_state.is_error:
                    return None
                current = result.next_state
            return self._proof_state_cache.get(state.stable_hash())
        except Exception:
            logger.warning("proof state rebuild failed", exc_info=True)
            return None
        finally:
            self._rebuilding = False

    async def _probe_longest_prefix(
        self, remaining: str, ps_id: int
    ) -> tuple[str, str, dict]:
        """Find where the next tactic ends by asking Lean, longest first.

        Returns (executed_text, rest, response). Every rejected candidate is a
        parse error: ~1ms, and it neither runs anything nor changes any proof
        state, so exactly one candidate executes.

        Longest-first is required, not an optimisation. A truncated construct
        can be perfectly valid syntax —
        "induction n with | zero => simp | succ k ih => rw [x]" parses fine and
        fails later with "unsolved goals" — so a shortest-first scan would
        accept it and reintroduce the truncation bug this replaced.
        """
        candidates = [remaining]
        candidates += [remaining[:c] for c in reversed(_candidate_boundaries(remaining))]
        smallest_failure: Optional[tuple[str, dict]] = None
        for cand in candidates:
            text = cand.strip()
            if not text:
                continue
            response = await self._send({"tactic": text, "proofState": ps_id})
            if _is_parse_error(response):
                # Keep the SHORTEST failing candidate, not the first. Lean
                # reports an unrecognised tactic name as a parse error too
                # ("<input>:1:1: unknown tactic"), so when nothing parses the
                # smallest unit we tried is the one that isolates the problem.
                # Reporting the longest instead told the model that
                # "bogus_xyz; exact h" was one failing step, when the real
                # fault was `bogus_xyz` alone.
                smallest_failure = (text, response)
                continue
            rest = remaining[len(cand):].lstrip()
            if rest.startswith(";"):
                rest = rest[1:].lstrip()
            return text, rest, response
        if smallest_failure is not None:
            text, response = smallest_failure
            return text, "", response
        return remaining.strip(), "", {"message": "Lean error:\nempty tactic"}

    async def _discover_steps(
        self, tactic: str, ps_id: int
    ) -> list[tuple[str, dict]]:
        """Run a candidate as a sequence of steps, Lean deciding the splits.

        Returns [(text, response), ...] in execution order; the final entry may
        be a failure. Stops early on failure or once the proof closes.
        """
        steps: list[tuple[str, dict]] = []
        remaining = tactic.strip()
        current = ps_id
        while remaining:
            peeled = _peel_bare_have(remaining)
            if peeled:
                # Deliberate decomposition, not a parsing question — the whole
                # string parses, so Lean must not be asked here.
                text, remaining = peeled
                response = await self._send({"tactic": text, "proofState": current})
            else:
                text, remaining, response = await self._probe_longest_prefix(
                    remaining, current
                )
            steps.append((text, response))
            if ("proofState" not in response
                    or "message" in response
                    or _has_error_messages(response)):
                break
            current = response["proofState"]
            if response.get("proofStatus", "") == "Completed":
                break
        return steps

    async def step(
        self,
        state: ProofState,
        tactic: str,
    ) -> StepResult:
        """
        Apply a tactic to a proof state. Used in SubprocessExecutor.step().

        Looks up the REPL proofState id for the given state, sends the
        tactic, and parses the response into a StepResult.

        worker.step(): step() sends a tactic to the REPL and waits for the result. This also involves multiple async steps:
        1. Send the tactic to the REPL (async because it writes to the subprocess stdin).
        2. Wait for the REPL to respond with the new proof state and success/failure info (async because it reads from the subprocess stdout).

        If tactic is a top-level ';'-chain (e.g. "intro n; simp"), it is
        split (see _split_top_level_tactics) and each step is sent to the
        REPL as its own sequential call, chaining proofState ids forward —
        the REPL only parses one atomic tactic per call, so an unsplit
        chain is rejected outright regardless of whether it's
        mathematically sound. This also localizes a mid-chain failure to
        the specific step that caused it (see _annotate_chain_error)
        instead of an opaque terminal error. Single-tactic candidates (the
        common case) take exactly one loop iteration and are unaffected.
        """
        start = time.perf_counter()

        # Look up the REPL proof state id for this state, stable_hash identifies which branch of the proof tree we are on within the workers' REPL process.
        repl_ps_id = self._proof_state_cache.get(state.stable_hash())
        # error out if we dont have this state in our cache. This should not happen if our caching and routing logic is correct,
        # but we check just in case.
        if repl_ps_id is None:
            # The cache is wiped when a stuck tactic forces the subprocess to
            # be killed (see the TimeoutError branch in _send). Every state the
            # Ledger is holding then points at REPL ids that no longer exist,
            # so WITHOUT recovery the rest of the run is spent on a Lean that
            # has forgotten everything. Measured: one 155s `simp` killed the
            # worker on turn 9 of imo2026_q1_terminal_value and the remaining
            # 41 of 49 turns never reached Lean at all — a void run that reads
            # in the results exactly like a model failure.
            #
            # A ProofState carries the full tactic path from the root, so the
            # state can be re-derived: reset the theorem and replay the trace.
            repl_ps_id = await self._rebuild_state(state)

        if repl_ps_id is None:
            error_state = ProofState(
                goals=state.goals,
                # Distinguishable on purpose: the search stops the trial on
                # this rather than spending its remaining budget.
                error=WORKER_LOST_ERROR,
                depth=state.depth,
                tactic_trace=state.tactic_trace,
            )
            return StepResult(
                next_state=error_state,
                tactic=tactic,
                elapsed_ms=(time.perf_counter() - start) * 1000,
            )

        # ---- Let Lean decide where each step ends. ----
        #
        # _split_top_level_tactics models a fragment of the Lean grammar by
        # hand, and has been wrong five separate times: '<;>', nested 'by',
        # ⟨⟩ depth, 'with |' alternative bodies, '·' focus blocks, and
        # 'case'/'next'/'conv' bodies. Each miss silently mutilated a correct
        # tactic — imo2026_q3_spec_share_bounds sent
        # "induction xs with | nil => intro a" and nothing else, thirteen
        # times running, while the model rewrote a branch that had never been
        # sent. Constructs it still gets wrong exist today ("first | t; t | t",
        # "repeat t; t", "iterate n t; t" all parse whole).
        #
        # So the grammar model is no longer load-bearing. Candidate cut points
        # come from bracket depth alone (unambiguous), and Lean is asked which
        # of them is real: the longest prefix it parses IS the next tactic.
        # An unknown construct now costs a millisecond instead of a mangling.
        try:
            steps = await self._discover_steps(tactic, repl_ps_id)
        except LeanREPLError as e:
            # The worker was killed or drained; re-running would pay twice.
            return StepResult(
                next_state=ProofState(
                    goals=state.goals,
                    error=str(e),
                    depth=state.depth,
                    tactic_trace=state.tactic_trace,
                ),
                tactic=tactic,
                elapsed_ms=(time.perf_counter() - start) * 1000,
            )

        if not steps:
            error_state = ProofState(
                goals=state.goals,
                error="Lean error:\nempty tactic",
                depth=state.depth,
                tactic_trace=state.tactic_trace,
            )
            return StepResult(
                next_state=error_state,
                tactic=tactic,
                elapsed_ms=(time.perf_counter() - start) * 1000,
            )

        sub_tactics = [text for text, _ in steps]
        current_ps_id = repl_ps_id
        response: dict = {}
        intermediate_states: list[ProofState] = []
        # The sub-steps Lean actually ran, in order. NOT the same as the
        # tactic the director wrote: _discover_steps splits chains and
        # _peel_bare_have rewrites `have h : T := by tac` into a bare
        # `have h : T`. tactic_trace must record what ran, or the trace we
        # print is not a proof. See the comment at the closed-state build.
        executed: list[str] = []

        for step_idx, (sub_tactic, response) in enumerate(steps):
            # Parse response. Note that response is a JSON object which contains keys like proofState, goals, proofStatus, etc...
            if "message" in response:
                # Tactic failed (REPL top-level error string)
                error_state = ProofState(
                    goals=state.goals,
                    error=_annotate_chain_error(response["message"], sub_tactics, step_idx),
                    depth=state.depth,
                    tactic_trace=state.tactic_trace,
                )
                return StepResult(
                    next_state=error_state,
                    tactic=tactic,
                    elapsed_ms=(time.perf_counter() - start) * 1000,
                    intermediate_states=tuple(intermediate_states),
                )

            # The REPL can also report errors via a "messages" list even when it
            # returns goals:[] — e.g. `exact bad_term` closes the goal syntactically
            # but reports "Unknown identifier" in messages. Treat those as failures.
            #
            # OPEN QUESTION — "internal exception #5". That is Lean's
            # `abortTactic` (index 5 of Lean.internalExceptionsRef, read out of
            # a live REPL). Lean throws it *after* logging the real error, so it
            # normally means "unsolved goals" and the useful text should be
            # alongside it. It showed up in older traces but did NOT occur once
            # in the first fully instrumented run, and four attempts to
            # reproduce it synthetically failed — it is neither the heartbeat
            # limit nor maxRecDepth, which both emit their own distinct
            # messages. If you see it again, do not theorise: read the whole
            # response body out of the raw log (traces/eval_*/lean/*.jsonl,
            # written under --trace) and check whether `messages` carries the
            # real error. Every other observed failure mode reaches the model
            # with the complete error verbatim, so an empty `messages` here
            # would be the one place the model is genuinely underinformed.
            # (An earlier note claimed a director had abandoned a true lemma
            # BECAUSE of an opaque failure like this. That was not supported:
            # falsity assertions turned out to be slightly anti-correlated
            # with visible crashes, 17% vs a 24% base rate.)
            msg_errors = [
                m for m in response.get("messages", [])
                if m.get("severity") == "error"
            ]
            if msg_errors:
                error_msg = "Lean error:\n" + msg_errors[0].get("data", "unknown error")
                error_state = ProofState(
                    goals=state.goals,
                    error=_annotate_chain_error(error_msg, sub_tactics, step_idx),
                    depth=state.depth,
                    tactic_trace=state.tactic_trace,
                )
                return StepResult(
                    next_state=error_state,
                    tactic=tactic,
                    elapsed_ms=(time.perf_counter() - start) * 1000,
                    intermediate_states=tuple(intermediate_states),
                )

            # This step succeeded
            if "proofState" not in response:
                error_state = ProofState(
                    goals=state.goals,
                    error=f"unexpected REPL response (no proofState): {response}",
                    depth=state.depth,
                    tactic_trace=state.tactic_trace,
                )
                return StepResult(
                    next_state=error_state,
                    tactic=tactic,
                    elapsed_ms=(time.perf_counter() - start) * 1000,
                    intermediate_states=tuple(intermediate_states),
                )

            current_ps_id = response["proofState"]
            executed.append(sub_tactic)
            if response.get("proofStatus", "") == "Completed":
                # Goal closed before exhausting the chain — nothing left to
                # prove, so remaining steps (which would error on "no
                # goals" if run anyway) don't need to execute.
                break

            # A genuinely verified checkpoint — everything up through this
            # sub-step compiled. Expose it so the search can later choose
            # to continue from here even if a *later* step in this same
            # chain (this one or a future candidate) turns out to be a
            # dead end, instead of only ever having "the whole chain" as
            # an atomic, all-or-nothing unit. Skip the last sub-tactic:
            # its outcome becomes next_state below, not an intermediate.
            if step_idx < len(sub_tactics) - 1:
                goals_raw = response.get("goals", [])
                if goals_raw:
                    checkpoint = ProofState(
                        goals=_parse_goals(goals_raw),
                        depth=state.depth + step_idx + 1,
                        tactic_trace=state.tactic_trace + tuple(sub_tactics[:step_idx + 1]),
                    )
                    # Must cache now, at the same point the REPL id is
                    # actually known — a future turn choosing to continue
                    # from this checkpoint calls step() with only the
                    # ProofState, which looks itself up via stable_hash().
                    self._proof_state_cache[checkpoint.stable_hash()] = current_ps_id
                    intermediate_states.append(checkpoint)

        elapsed = (time.perf_counter() - start) * 1000

        # From here on, `response` is whichever sub-step actually ran last
        # (the whole chain if all steps succeeded, or the step that closed
        # the goal early) — identical to the pre-chaining single-tactic path.
        new_repl_ps_id = current_ps_id
        goals_raw = response.get("goals", [])
        proof_status = response.get("proofStatus", "")

        if proof_status == "Completed":
            # Proof closed.
            #
            # tactic_trace records `executed`, not `tactic`. These differ
            # whenever the chain was split or a `have ... := by ...` was
            # peeled, and recording the director's original string produced a
            # proof_trace that does not replay: measured on
            # eval_20260902_140914 (imo2005_q3, solved 2/2), pasting the
            # recorded trace back into Lean as one command failed with "No
            # goals to be solved". The trace said
            #   have hB : … ≠ 0 := by positivity; have hD : … ; field_simp; ring
            # while Lean was actually sent the peeled `have hB : … ≠ 0` and
            # the rest as separate steps against a different goal. Checkpoints
            # (below) already recorded `sub_tactics`; only the two terminal
            # states did not, so a single trace mixed both conventions.
            closed_state = ProofState(
                goals=(),
                depth=state.depth + 1,
                tactic_trace=state.tactic_trace + tuple(executed),
            )
            return StepResult(
                next_state=closed_state,
                tactic=tactic,
                elapsed_ms=elapsed,
                intermediate_states=tuple(intermediate_states),
            )

        if not goals_raw:
            # goals is empty but proofStatus is NOT "Completed" — e.g.
            # "Incomplete: contains sorry". This happens with apply?/exact?
            # when no full match is found: Lean reports no goals left to
            # display, but the proof term itself is incomplete. Treat as a
            # failed tactic, not a close — accepting it as a "next_state"
            # with empty goals would independently re-derive is_closed=True
            # downstream (ProofState.is_closed only checks len(goals) == 0),
            # silently reproducing the same false-success bug.
            error_state = ProofState(
                goals=state.goals,
                error=(
                    "Lean error:\nTactic reported no remaining goals but "
                    f"proofStatus={proof_status!r} (not Completed) — likely "
                    "inserted a hidden sorry/placeholder."
                ),
                depth=state.depth,
                tactic_trace=state.tactic_trace,
            )
            return StepResult(
                next_state=error_state,
                tactic=tactic,
                elapsed_ms=elapsed,
                intermediate_states=tuple(intermediate_states),
            )

        next_state = ProofState(
            goals=_parse_goals(goals_raw),
            depth=state.depth + 1,
            tactic_trace=state.tactic_trace + tuple(executed),
        )

        # Cache the new proof state
        self._proof_state_cache[next_state.stable_hash()] = new_repl_ps_id

        return StepResult(
            next_state=next_state,
            tactic=tactic,
            elapsed_ms=elapsed,
            intermediate_states=tuple(intermediate_states),
        )


class SubprocessExecutor:
    """
    Wraps a single LeanWorker, implementing the LeanExecutor protocol.

    One SubprocessExecutor = one `lake exe repl` subprocess = one proof search.
    For k parallel searches, create k SubprocessExecutor instances and run
    them concurrently with asyncio.gather().

    The lock serializes reset() and step() so the REPL's stdin/stdout
    is never written to concurrently within the same Python process.
    """

    def __init__(
        self,
        lean_project_dir: Path = LEAN_PROJECT_DIR,
        load_mathlib: bool = True,
        raw_log_path: Optional[Path] = None,
    ):
        self._dir = lean_project_dir
        self._load_mathlib = load_mathlib
        self._worker: Optional[LeanWorker] = None
        self._lock = asyncio.Lock()
        self._started = False
        # When set, every REPL exchange is appended to this JSONL file.
        self._raw_log_path = raw_log_path

    async def start(self) -> None:
        """Start the Lean worker process. Must be called before use."""
        self._worker = LeanWorker(
            self._dir,
            load_mathlib=self._load_mathlib,
            raw_log_path=self._raw_log_path,
        )
        await self._worker.start()
        self._started = True
        logger.info("Started Lean worker")

    def set_raw_log_path(self, path: Optional[Path]) -> None:
        """
        Point this executor's raw REPL log at *path* (or disable with None).

        Settable after start() because the eval harness only decides the run
        directory — which is keyed by a timestamp generated inside run_eval —
        after the executors have already been constructed and had Mathlib
        loaded. Sets it on the live worker too, so it takes effect for the
        current process rather than only after a restart.
        """
        self._raw_log_path = path
        if self._worker is not None:
            self._worker._raw_log_path = path

    async def reset(self, theorem: str, preamble: str = "") -> ProofState:
        """Initialize a new proof attempt and return the initial ProofState."""
        async with self._lock:
            # If the subprocess was killed (e.g., due to a stuck drain timeout),
            # restart it before attempting a new proof.
            if not self._worker._proc or self._worker._proc.returncode is not None:
                logger.warning("Lean worker process is dead; restarting...")
                await self._worker.start()
            state, _ = await self._worker.reset(theorem, preamble)
        return state

    async def step(self, state: ProofState, tactic: str) -> StepResult:
        """Apply a tactic to the given proof state and return the result.

        The REPL is single-threaded, so the lock ensures that concurrent
        Python callers do not interleave their writes to stdin/stdout.

        The REPL supports branching: sending two different tactics with the
        same proofState ID produces two independent new proof states.

            send: {"tactic": "intro n", "proofState": 0}
            recv: {"proofState": 1, "goals": [...]}

            send: {"tactic": "simp", "proofState": 0}   ← same ID
            recv: {"proofState": 2, "goals": [...]}       ← independent new ID

        This lets the search explore multiple branches from one state without
        restarting the REPL, since each branch gets its own ID in the REPL's
        internal proof state table.
        """
        async with self._lock:
            return await self._worker.step(state, tactic)

    async def close(self) -> None:
        """Shut down the worker process."""
        if self._worker:
            await self._worker.stop()
            self._worker = None
        logger.info("Lean worker stopped")


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def _parse_goals(goals_raw: list[str]) -> tuple[Goal, ...]:
    """Wrap the REPL's raw `goals` strings as Goals, verbatim.

    Deliberately no parsing: see Goal's docstring. Lean's rendering is the
    authority on what the proof position is, and every attempt to rebuild it
    from parts lost information — 890 of 3704 recorded goals were corrupted
    before this was removed.
    """
    return tuple(Goal(text=g.strip()) for g in goals_raw if g and g.strip())


