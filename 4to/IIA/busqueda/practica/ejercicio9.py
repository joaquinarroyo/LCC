from Problem import Problem


class getSeven(Problem):

    def initial(self):
        return self.initial

    def actions(self, state):
        actions = []
        if state == 0:
            return [(1, 1, " 1")]
        elif state % 3 == 0:
            return [(state/3, (2*state)/3, " /3")]
        else:
            actions += [(state + 1, 1, " +1")]
            actions += [(state - 1, 1, " -1")]
            actions += [(state * 2, state, " *2")]
            actions += [(1, 1, " 1")]
            return actions

    def goal_test(self, state):
        return state == self.goal

    def heuristic(self, state):
        return abs(self.goal - state)


def a_star(problem):
    node = (problem.initial, 0, str(problem.initial))
    frontier = [node]
    closed = []
    while frontier:
        state, cost, actions = frontier.pop()
        if problem.goal_test(state):
            return state, cost, actions

        if state not in closed:
            closed += [state]
            for c_state, c_cost, c_action in problem.actions(state):
                frontier += [(c_state, cost + c_cost, actions + c_action)]

        frontier.sort(key=lambda x: problem.heuristic(
            x[0]) + x[1], reverse=True)


problem = getSeven(1, 25)
print(a_star(problem))
