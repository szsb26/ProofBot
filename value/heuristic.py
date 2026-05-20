"""
Heuristic value model based on proof state structure.

Requires no training data and no ML. Used in Phases 1-2 before
enough search logs exist to train a real value model.

The heuristic is based on two observations:
    1. Fewer open goals = more promising (closer to done)
    2. Shallower depth = more promising (less likely to be stuck)

This is surprisingly competitive with a poorly-trained value model,
because early in the project you won't have enough data to train
a model that beats this simple baseline.
"""

from __future__ import annotations
import math

from core.proof_state import ProofState
from core.value import ValueModel


class HeuristicValue:
    """
    Estimates proof state value using goal count and search depth.
    Satisfies the ValueModel protocol.

    The formula is:
        value = exp(-(goal_weight * num_goals + depth_weight * depth))

    This gives:
        - A state with 0 goals (closed) -> value = 1.0
        - Each additional open goal reduces value exponentially
        - Each additional depth level reduces value slightly
    """

    def __init__(
        self,
        goal_weight: float = 1.0,
        depth_weight: float = 0.05,
    ):
        """
        Args:
            goal_weight:  How much each open goal penalizes the value.
                          Higher = more aggressive pruning of multi-goal states.
            depth_weight: How much each depth level penalizes the value.
                          Keep small — depth is a weak signal compared to goals.
        """
        self.goal_weight = goal_weight
        self.depth_weight = depth_weight

    def evaluate(self, state: ProofState) -> float:
        """
        Estimate value using goal count and depth.

        Edge cases:
            - Closed state:  returns 1.0 (certain success)
            - Error state:   returns 0.0 (dead branch)
            - Open state:    returns value in (0, 1)
        """
        if state.is_closed:
            return 1.0
        if state.is_error:
            return 0.0

        penalty = (
            self.goal_weight * state.num_goals
            + self.depth_weight * state.depth
        )
        return math.exp(-penalty)
