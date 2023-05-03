from Problem import Problem


class getSeven(Problem):

    def initial(self):
        return self.initial

    def actions(self, state):
        actions = []
        if state == 0:
            return [(1, 1)]
        elif state % 3 == 0:
            return [(state/3, (2*state)/3)]
        else:
            actions += [(state + 1, 1)]
            actions += [(state - 1, 1)]
            actions += [(state * 2, state)]
            actions += [(1, 1)]
            return actions

    def goal_test(self, state):
        return state == self.goal

    def heuristic(self, state):
        return abs(self.goal - state)


def a_star(problem):
    node = (problem.initial, [], 0)
    frontier = [node]
    closed = []
    while frontier:
        state, actions, cost = frontier.pop()
        if problem.goal_test(state):
            return state, actions, cost

        if state not in closed:
            closed += [state]
            for c_state, c_cost in problem.actions(state):
                frontier += [(c_state, actions + [c_state], cost + c_cost)]

        frontier.sort(key=lambda x: problem.heuristic(x[0]) + x[2], reverse=True)


if __name__ == '__main__':
    init, goal = 1, 25
    problem = getSeven(init, goal)
    print(a_star(problem))
