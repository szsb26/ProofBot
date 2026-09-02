"""
Core data structures representing a Lean proof state.

These are pure Python dataclasses with no dependencies on Lean, any API,
or any ML library. Every other module in this codebase speaks in terms
of these types.
"""

from __future__ import annotations
from dataclasses import dataclass, field
import hashlib
import json
import re


@dataclass(frozen=True)
class Goal:
    """
    A single open goal, held EXACTLY as Lean printed it.

    A goal is a self-contained sub-theorem: the hypotheses you may assume,
    then `⊢` and the target to prove. Example:

        n : ℕ
        h : n > 0
        ⊢ n + 0 = n

    `text` is Lean's own bytes, verbatim. It is deliberately NOT split into
    hypothesis/target fields.

    Why: it used to be. `_parse_goal_string` read the text line by line,
    treating anything containing " : " as a hypothesis, and Lean wraps long
    lines. A hypothesis whose type wrapped lost its name line (no " : ") AND
    its continuation lines, so it vanished; a target that wrapped was cut off
    after its first line; and a continuation line that happened to contain a
    colon was rendered as an invented hypothesis. Measured across 3704
    recorded goals: 890 corrupted (24%) — 653 deleted hypotheses, 468
    truncated targets, 305 fabricated ones. Of 1061 deleted hypotheses the
    large majority were the model's own `have` sub-lemmas (218 named `key`),
    because a decomposition is exactly the kind of long statement that wraps.

    Both consumers of the old fields wanted the text back anyway: serialize()
    glued them into a string for the prompt, and stable_hash() hashed them.
    So the decomposition was pure loss, and the model was shown goals with
    its own lemmas missing and targets cut off mid-expression. It said so, 53
    times across 20 traces ("the goal displays only '⊢ ∀ (n : ℕ),' which is
    truncated/abnormal"), and blamed its own tactics, having no way to see
    that a rendering layer existed.
    """
    text: str

    def serialize(self) -> str:
        return self.text


# NOTE: Lean's case label ("case succ") is deliberately NOT stripped, though
# it looks like a mere tag. Two goals identical apart from it were observed 18
# times, and merging them is tempting — but the model addresses goals BY that
# label ("case pos => exact MulanWins.win hin"), so merging lets such a tactic
# land on the wrong one. Under-splitting states is precisely the failure this
# module was rewritten to remove; over-splitting costs 18 extra frontier
# entries out of 1177 and is never wrong.
# Inaccessible names print as `h✝`, and `h✝¹`, `h✝²` … when shadowed. The
# numbering is positional, so a renumbering must not read as a new state.
_INACCESSIBLE_RE = re.compile("✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*")
# Metavariable ids (`?m.470`) are allocation counters, not mathematics.
_METAVAR_RE = re.compile(r"\?[mu]\.\d+")


def _normalise_for_hash(text: str) -> str:
    """Drop the parts of a goal's rendering that can differ without the proof
    position differing.

    Deliberately minimal. Verified against 1177 distinct recorded goals: this
    normalisation merges nothing that was otherwise distinct, so it costs no
    deduplication today and only guards against a renumbering tomorrow. Every
    other difference in Lean's text is treated as a different state — after a
    parser merged 17 buckets of genuinely different goals, the bias here is
    firmly toward splitting rather than merging."""
    t = _INACCESSIBLE_RE.sub("✝", text)
    t = _METAVAR_RE.sub("?", t)
    return "\n".join(line.rstrip() for line in t.strip().split("\n"))


@dataclass(frozen=True)
class ProofState:
    """
    The complete state of a proof at a given point in the search tree. A proof state consists of a list of open goals, and
    metadata about the proof search process (error message, depth, tactic trace).

    Immutable. Every field is set at construction; nothing mutates.
    The hash is deterministic so ProofState can be used as a dict key
    and cached via lru_cache.

    Note that since we are using frozen dataclass decorator,__init__, __repr__, __eq__, and __hash__ methods are automatically generated,
    so self variables like goals, error, etc... are self variables and its as if we wrote these in the __init__method. For ex.,
    
    def __init__(self, goals: tuple[Goal, ...], error: str | None = None, depth: int = 0, tactic_trace: tuple[str, ...] = ()):
        self.goals = goals
        self.error = error
        self.depth = depth
        self.tactic_trace = tactic_trace

    Attributes:
        goals:        Remaining open subgoals. Empty means proof is closed.
        error:        If the last tactic failed, the error message. None otherwise.
        depth:        How many tactics have been applied to reach this state.
        tactic_trace: The sequence of tactics applied to reach this state.
    """
    goals: tuple[Goal, ...]
    error: str | None = None
    depth: int = 0
    tactic_trace: tuple[str, ...] = field(default_factory=tuple)

    @property
    def is_closed(self) -> bool:
        """True when all goals are discharged and no error occurred."""
        return len(self.goals) == 0 and self.error is None

    @property
    def is_error(self) -> bool:
        """True when the last tactic produced an error."""
        return self.error is not None

    @property
    def num_goals(self) -> int:
        return len(self.goals)

    def serialize(self) -> str:
        """
        Produce a human-readable string suitable for use as an LLM prompt.
        This is the representation the policy model will see.
        """
        if self.is_closed:
            return "[PROOF CLOSED]"
        if self.is_error:
            return f"[ERROR] {self.error}"
        parts = []
        for i, goal in enumerate(self.goals):
            if len(self.goals) > 1:
                parts.append(f"Goal {i + 1}/{len(self.goals)}:")
            parts.append(goal.serialize())
        return "\n\n".join(parts)

    def stable_hash(self) -> str:
        """
        Deterministic hash of this proof state for use as a cache key.
        Does not include depth or tactic_trace — two states with identical
        goals reached by different paths hash identically, which is correct:
        the REPL result of applying a tactic depends only on the goal state.
        """
        content = json.dumps(
            [_normalise_for_hash(goal.text) for goal in self.goals],
            sort_keys=True,
        )
        return hashlib.sha256(content.encode()).hexdigest()[:16]


# ---------------------------------------------------------------------------
# Convenience constructors
# ---------------------------------------------------------------------------

def make_goal(target: str, hypotheses: list[tuple[str, str]] | None = None) -> Goal:
    """
    Convenience constructor for tests and quick scripting.

    Usage:
        make_goal("n + 0 = n", [("n", "ℕ"), ("h", "n > 0")])
    """
    lines = [f"{name} : {type_}" for name, type_ in (hypotheses or [])]
    lines.append(f"⊢ {target}")
    return Goal(text="\n".join(lines))


def make_proof_state(
    targets: list[str],
    hypotheses: list[list[tuple[str, str]]] | None = None,
    depth: int = 0,
) -> ProofState:
    """
    Convenience constructor for tests and quick scripting.

    Usage:
        make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])
    """
    hyps_list = hypotheses or [[] for _ in targets]
    goals = tuple(
        make_goal(target, hyps)
        for target, hyps in zip(targets, hyps_list)
    )
    return ProofState(goals=goals, depth=depth)
