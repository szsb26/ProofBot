"""
Abstract interface for the value model.

The ValueModel protocol estimates P(proof succeeds | current state).
It is used by the search algorithm to prioritize promising branches
without doing full rollouts — exactly the role of the value head in
AlphaZero.

Implementations (in order of sophistication):
    value/heuristic.py  -> HeuristicValue   (Phase 1-2, no ML)
    value/trained.py    -> TrainedValue     (Phase 3+, trained classifier)
    value/process.py    -> ProcessValue     (Phase 4, step-level PRM)
"""

from __future__ import annotations
from typing import Protocol, runtime_checkable

from core.proof_state import ProofState


@runtime_checkable
class ValueModel(Protocol):
    """
    Protocol for estimating the value of a proof state.

    The value is a scalar in [0, 1] representing the estimated
    probability that a proof can be found from this state:
        0.0 = almost certainly a dead end
        1.0 = almost certainly provable from here

    Used in MCTS to:
        1. Bootstrap Q(s,a) at depth-limit leaves instead of doing
           full rollouts (too expensive with Lean REPL calls).
        2. Prioritize which branches to explore in best-first search.

    The search loop calls evaluate() at every leaf node that hasn't
    been terminated (closed or errored). The returned value is then
    backpropagated up the tree as part of Q(s,a) updates.
    """

    def evaluate(self, state: ProofState) -> float:
        """
        Estimate the probability of proof success from this state.

        Args:
            state: The current proof state to evaluate.
                   Should not be closed or an error state — the search
                   loop only calls this on live, open states.

        Returns:
            A float in [0.0, 1.0].
            Higher = more promising.
            0.0 is returned for clearly hopeless states.
            1.0 would mean certain success (rare in practice).
        """
        ...
