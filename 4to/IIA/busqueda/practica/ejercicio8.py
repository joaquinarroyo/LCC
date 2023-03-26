from Problem import Problem


class CongifProblem(Problem):

    def initial(self):
        return self.initial

    def actions(self, state):
        actions = []
        for i in range(len(state) - 1):
            actions += [(swap(state, i, i+1), 1, f"swap {i} {i+1}, ")]
        return actions

    def goal_test(self, state):
        return state == self.goal

    def heuristic(self, state):
        return difference(state, self.goal)


def swap(state, i, j):
    state = list(state)
    state[i], state[j] = state[j], state[i]
    return state


def difference(state, goal):
    return sum([1 for i in range(len(state)) if state[i] != goal[i]])


def a_star(problem):
    node = (problem.initial, 0, "")
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


init = ['O', 'X', 'O', 'X', 'O', 'X', 'O', 'X']
goal = ['O', 'O', 'O', 'O', 'X', 'X', 'X', 'X']
problem = CongifProblem(init, goal)
print(a_star(problem))

# swap 3 4, swap 1 2, swap 2 3, swap 5 6, swap 4 5, swap 3 4
#              0    1    2    3    4    5    6    7
# init     = ['O', 'X', 'O', 'X', 'O', 'X', 'O', 'X']
# swap 3 4 = ['O', 'X', 'O', 'O', 'X', 'X', 'O', 'X']
# swap 1 2 = ['O', 'O', 'X', 'O', 'X', 'X', 'O', 'X']
# swap 2 3 = ['O', 'O', 'O', 'X', 'X', 'X', 'O', 'X']
# swap 5 6 = ['O', 'O', 'O', 'X', 'X', 'O', 'X', 'X']
# swap 4 5 = ['O', 'O', 'O', 'X', 'O', 'X', 'X', 'X']
# swap 3 4 = ['O', 'O', 'O', 'O', 'X', 'X', 'X', 'X']
