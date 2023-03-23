
class Problem:
    def __init__(self, initial, goal=None):
        self.initial = initial
        self.goal = goal

    def actions(self, state):
        raise NotImplementedError

    def goal_test(self, state):
        return state == self.goal

    def heuristic(self, state):
        return 0
