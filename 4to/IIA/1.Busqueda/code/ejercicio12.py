from Problem import Problem


class DividirPila(Problem):
    def __init__(self, initial, goal=None):
        super().__init__(initial, goal)

    def actions(self, state):
        actions = []
        for i in range(len(state)):
            i_ = state[i]
            if i_ != 2 and i_ != 1:
                for (i1, i2) in self.dividir(i_):
                    if i1 != i2:
                        state_ = state.copy()
                        del state_[i]
                        state_.append(i1)
                        state_.append(i2)
                        actions.append((state_, 2))
        return actions

    def goal_test(self, state):
        for i in state:
            if i != 2 and i != 1:
                return False
        return True

    def h(self, state):
        return len(state) + self.contar(state)

    def contar(self, state):
        cont = 0
        for i in state:
            if i != 2 and i != 1:
                cont += 1
        return cont

    def dividir(self, n):
        l = []
        for i in range(1, n):
            l.append((i, n - i))
        return l


def a_star(problem):
    node = (problem.initial, [], 0)
    frontier = [node]
    closed = []
    while frontier:
        state, actions, cost = frontier.pop()

        if problem.goal_test(state):
            return state, actions, cost

        for succ, cost_ in problem.actions(state):
            if succ not in closed:
                closed.append(succ)
                frontier.append((succ, actions + [succ], cost + cost_))
        frontier.sort(key=lambda x: problem.h(x[0]))
    return None


if __name__ == '__main__':
    problem = DividirPila([7])
    _, actions, cost = a_star(problem)
    print(actions, cost)
