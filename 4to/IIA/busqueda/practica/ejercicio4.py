import copy
from Problem import Problem


# Ejercicio 4 #
# busqueda en ancho
def bfs(problem):
    l = [(problem.initial, [])]

    while l:
        node, actions = l.pop(0)

        if problem.goal_test(node):
            return node, actions

        for succ, action, _ in problem.actions(node):
            l += [(succ, actions + [action])]


# busqueda en profundidad
def dfs(problem):
    l = [(problem.initial, [])]

    while l:
        node, actions = l.pop()

        if problem.goal_test(node):
            return node, actions

        for succ, action, _ in problem.actions(node):
            l += [(succ, actions + [action])]


# busqueda en profundidad con ancestros
def dfs_with_ancestors(problem):
    l = [(problem.initial, [], [])]

    while l:
        node, ancestors, actions = l.pop()

        if problem.goal_test(node):
            return node, actions

        for succ, action, _ in problem.actions(node):
            if succ not in ancestors:
                newAncestors = ancestors + [node]
                l += [(succ, newAncestors, actions + [action])]


# busqueda en profundidad con altura limite
def dfs_with_limit(problem, limit):
    l = [(problem.initial, [], [], 0)]

    while l:
        node, ancestors, actions, depth = l.pop()

        if problem.goal_test(node):
            return node, actions

        if depth < limit:
            for succ, action, _ in problem.actions(node):
                if succ not in ancestors:
                    newAncestors = ancestors + [node]
                    l += [(succ, newAncestors, actions + [action], depth + 1)]


# A estrella
def a_star(problem):
    l = [(problem.initial, [], [], 0)]
    while l:
        node, ancestors, actions, depth = l.pop()
        if problem.goal_test(node):
            return node, actions
        for succ, action, _ in problem.actions(node):
            # Chequeamos los ancestros
            if succ not in ancestors:
                newAncestors = ancestors + [node]
                l += [(succ, newAncestors, actions + [action], depth + 1)]
        # Ordenamos segun la heuristica y costo
        l.sort(key=lambda x: problem.heuristic(x[0]) + x[3], reverse=True)


# Problema de los ocho numeros
class EightPuzzle(Problem):

    def __init__(self):
        initial = [[2, 8, 3], [1, 6, 4], [7, 0, 5]]
        goal = [[1, 2, 3], [8, 0, 4], [7, 6, 5]]
        super().__init__(initial, goal)

    def actions(self, state):
        actions = []
        newStates = []
        (iz, jz) = self.search_zero(state)
        if iz > 0:
            actions += [(iz - 1, jz, "arriba")]
        if iz < 2:
            actions += [(iz + 1, jz, "abajo")]
        if jz > 0:
            actions += [(iz, jz - 1, "izquierda")]
        if jz < 2:
            actions += [(iz, jz + 1, "derecha")]
        for (i, j, action) in actions:
            newState = copy.deepcopy(state)
            newState[i][j], newState[iz][jz] = newState[iz][jz], newState[i][j]
            newStates += [(newState, action, 1)]
        return newStates

    def heuristic(self, state):
        return self.manhattan_distance(state)

    def goal_test(self, state):
        return state == self.goal

    def search_zero(self, state):
        for i in range(0, 3):
            for j in range(0, 3):
                if state[i][j] == 0:
                    return i, j
        return None

    def count_diff(self, state):
        count = 0
        for i in range(0, 3):
            for j in range(0, 3):
                if state[i][j] != self.goal[i][j]:
                    count += 1
        return count

    # Calcula la distancia entre el valor y su posicion en el estado objetivo
    def manhattan_distance(self, state):
        count = 0
        for i in range(0, 3):
            for j in range(0, 3):
                if state[i][j] != self.goal[i][j]:
                    count += self.distance(i, j, state[i][j])
        return count

    def distance(self, i, j, value):
        for k in range(0, 3):
            for l in range(0, 3):
                if self.goal[k][l] == value:
                    return abs(i - k) + abs(j - l)
        return None


if __name__ == "__main__":
    problem = EightPuzzle()
    node, actions = bfs(problem)
    print(node)
    print(actions)
