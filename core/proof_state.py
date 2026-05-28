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


@dataclass(frozen=True)
class Hypothesis:
    """
    A single hypothesis in the local context of a goal. We can think of this as already established facts that we can use to prove the goal.
    Frozen classes are immutable, so once a Hypothesis is created, its name and type cannot be changed. This makes it easier to reason about 
    the proof state and ensures that the hash of a ProofState is stable.
    
    Example: given `h : n > 0`, name="h", type_="n > 0"
    """
    name: str
    type_: str

    def serialize(self) -> str:
        return f"{self.name} : {self.type_}"


@dataclass(frozen=True)
class Goal:
    """
    A single open goal: a list of hypotheses and a target to prove. The target is a proposition we want to prove, 
    and the hypotheses are the assumptions we can use to prove it. The |- symbol separates the hypotheses from the target in Lean.

    Example:
    hypotheses = [Hypothesis("n", "ℕ"), Hypothesis("h", "n > 0")]
    target = "n + 0 = n"
    """
    hypotheses: tuple[Hypothesis, ...]
    target: str

    def serialize(self) -> str:
        hyp_str = "\n".join(h.serialize() for h in self.hypotheses)
        if hyp_str:
            return f"{hyp_str}\n⊢ {self.target}"
        return f"⊢ {self.target}"


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
    # Identifies which proof search session produced this state.
    # Set by SubprocessExecutor.reset(); excluded from stable_hash() so
    # two sessions on the same theorem don't collide in the router.
    session_id: str = ""

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
            [
                [
                    [(h.name, h.type_) for h in goal.hypotheses],
                    goal.target,
                ]
                for goal in self.goals
            ],
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
    hyps = tuple(Hypothesis(name, type_) for name, type_ in (hypotheses or []))
    return Goal(hypotheses=hyps, target=target)


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
