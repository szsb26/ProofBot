"""
Unit tests for value/heuristic.py
"""

import pytest
import math
from core.proof_state import make_proof_state, ProofState
from core.value import ValueModel
from value.heuristic import HeuristicValue


class TestHeuristicValue:

    def test_satisfies_protocol(self):
        v = HeuristicValue()
        assert isinstance(v, ValueModel)

    def test_closed_state_returns_one(self):
        v = HeuristicValue()
        state = make_proof_state([])
        assert v.evaluate(state) == 1.0

    def test_error_state_returns_zero(self):
        v = HeuristicValue()
        state = ProofState(goals=(), error="simp failed")
        assert v.evaluate(state) == 0.0

    def test_open_state_between_zero_and_one(self):
        v = HeuristicValue()
        state = make_proof_state(["n + 0 = n"])
        value = v.evaluate(state)
        assert 0.0 < value < 1.0

    def test_fewer_goals_higher_value(self):
        v = HeuristicValue()
        one_goal = make_proof_state(["P"])
        two_goals = make_proof_state(["P", "Q"])
        three_goals = make_proof_state(["P", "Q", "R"])
        assert v.evaluate(one_goal) > v.evaluate(two_goals)
        assert v.evaluate(two_goals) > v.evaluate(three_goals)

    def test_shallower_depth_higher_value(self):
        v = HeuristicValue()
        shallow = make_proof_state(["n + 0 = n"], depth=1)
        deep = make_proof_state(["n + 0 = n"], depth=10)
        assert v.evaluate(shallow) > v.evaluate(deep)

    def test_depth_has_less_impact_than_goals(self):
        """One extra goal should hurt more than many extra depth levels.
        
        With default weights (goal=1.0, depth=0.05):
            one_goal_deep:      1*1.0 + 19*0.05 = 1.95  penalty
            two_goals_shallow:  2*1.0 +  0*0.05 = 2.00  penalty
        So one_goal_deep has lower penalty → higher value.
        """
        v = HeuristicValue()
        one_goal_deep = make_proof_state(["P"], depth=19)
        two_goals_shallow = make_proof_state(["P", "Q"], depth=0)
        assert v.evaluate(one_goal_deep) > v.evaluate(two_goals_shallow)

    def test_custom_weights(self):
        v = HeuristicValue(goal_weight=2.0, depth_weight=0.0)
        state = make_proof_state(["P"])
        expected = math.exp(-2.0 * 1)
        assert abs(v.evaluate(state) - expected) < 1e-9

    def test_zero_depth_weight(self):
        """With depth_weight=0, depth has no effect."""
        v = HeuristicValue(depth_weight=0.0)
        shallow = make_proof_state(["P"], depth=0)
        deep = make_proof_state(["P"], depth=100)
        assert abs(v.evaluate(shallow) - v.evaluate(deep)) < 1e-9

    def test_value_decreases_monotonically_with_goals(self):
        v = HeuristicValue(depth_weight=0.0)
        values = [
            v.evaluate(make_proof_state(["P"] * n))
            for n in range(1, 6)
        ]
        assert values == sorted(values, reverse=True)

    def test_value_in_valid_range(self):
        v = HeuristicValue()
        for num_goals in range(0, 5):
            for depth in [0, 5, 10, 50]:
                state = make_proof_state(
                    ["P"] * num_goals,
                    depth=depth
                )
                val = v.evaluate(state)
                assert 0.0 <= val <= 1.0
