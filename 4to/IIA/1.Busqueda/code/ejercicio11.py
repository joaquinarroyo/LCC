from Problem import Problem

class BWProblem(Problem):
    def __init__(self, initial, goal=None):
        Problem.__init__(self, initial, goal)

    def initial(self):
        return self.initial
    
    def actions(self, state):
        i = self.get_blank_position(state)
        actions = []
        for n in range(1, 4):
            r1 = self.move(state, i, 'R', n)
            r2 = self.move(state, i, 'L', n)
            if r1:
                actions += [(r1, n)]
            if r2:
                actions += [(r2, n)]
        return actions

    def move(self, state, i, direction, n):
        pred = state.copy()
        l = len(state) - 1
        if direction == 'R' and i <= l - n:
            pred[i], pred[i + n] = pred[i + n], pred[i]
            return pred
        elif direction == 'L' and i >= n:
            pred[i], pred[i - n] = pred[i - n], pred[i]
            return pred
        return None
            
    def get_blank_position(self, state):
        for i in range(len(state)):
            if state[i] == 0:
                return i
            
    def goal_test(self, state):
        return self.h(state) == 0

    def h(self, state):
        state_ = state.copy()
        state_.remove(0)
        result = 0
        for i in range(len(state_) - 2):
            result += state_[i] * self.p(state_[i])
        for i in range(2, len(state_)):
            result += state_[i] * self.q(state_[i])
        return result
    
    def p(self, n):
        if n == 1:
            return 1
        else:
            return 0
    
    def q(self, n):
        if n == 1:
            return 0
        else:
            return -1

def a_star(problem):
    node = (problem.initial, [], 0)
    frontier = [node]
    closed = []
    while frontier:
        node, actions, cost = frontier.pop()

        if problem.goal_test(node):
            return node, actions, cost

        for succ, cost_ in problem.actions(node):
            if succ not in closed:
                closed += [succ]
                frontier += [(succ, actions + [succ], cost + cost_)]
        frontier.sort(key=lambda x: problem.h(x[0]) + x[2], reverse=True)
    return None

if __name__ == '__main__':
    init = [1, 1, -1, -1, 0]
    problem = BWProblem(init)
    print(a_star(problem))