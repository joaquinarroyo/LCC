from Problem import Problem

# ejercicio 5 #

# a
cities = {
    "Arad": {"Zerind": 75, "Sibiu": 140, "Timisoara": 118},
    "Bucharest": {"Urziceni": 85, "Giurgiu": 90, "Pitesti": 101, "Fagaras": 211},
    "Craiova": {"Drobeta": 120, "Rimnicu": 146, "Pitesti": 138},
    "Drobeta": {"Mehadia": 75, "Craiova": 120},
    "Eforie": {"Hirsova": 86},
    "Fagaras": {"Sibiu": 99, "Bucharest": 211},
    "Giurgiu": {"Bucharest": 90},
    "Hirsova": {"Eforie": 86, "Urziceni": 98},
    "Iasi": {"Vaslui": 92, "Neamt": 87},
    "Lugoj": {"Timisoara": 111, "Mehadia": 70},
    "Mehadia": {"Lugoj": 70, "Drobeta": 75},
    "Neamt": {"Iasi": 87},
    "Oradea": {"Zerind": 71, "Sibiu": 151},
    "Pitesti": {"Rimnicu": 97, "Craiova": 138, "Bucharest": 101},
    "Rimnicu": {"Sibiu": 80, "Pitesti": 97, "Craiova": 146},
    "Sibiu": {"Arad": 140, "Oradea": 151, "Fagaras": 99, "Rimnicu": 80},
    "Timisoara": {"Arad": 118, "Lugoj": 111},
    "Urziceni": {"Bucharest": 85, "Hirsova": 98, "Vaslui": 142},
    "Vaslui": {"Iasi": 92, "Urziceni": 142},
    "Zerind": {"Arad": 75, "Oradea": 71},
}

distance_to_bucharest = {
    "Arad": 366,
    "Bucharest": 0,
    "Craiova": 160,
    "Drobeta": 242,
    "Eforie": 161,
    "Fagaras": 176,
    "Giurgiu": 77,
    "Hirsova": 151,
    "Iasi": 226,
    "Lugoj": 244,
    "Mehadia": 241,
    "Neamt": 234,
    "Oradea": 380,
    "Pitesti": 100,
    "Rimnicu": 193,
    "Sibiu": 253,
    "Timisoara": 329,
    "Urziceni": 80,
    "Vaslui": 199,
    "Zerind": 374,
}

class searchCity(Problem):
    def __init__(self, initial, goal, h=0):
        self.h = h
        super().__init__(initial, goal)

    def actions(self, state):
        actions = []
        for city in cities[state]:
            actions += [(city, "ir a " + city, cities[state][city])]
        return actions

    def goal_test(self, state):
        return state == self.goal

    def heuristic(self, x):
        match self.h:
            case 0:
                # Heuristica a, costo
                return x[2]
            case 1:
                # Heuristica b, distancia a bucharest
                return self.distance_heuristic(x[0])
            case 2:
                # Heuristica c, distancia a bucharest + costo
                return self.distance_heuristic(x[0]) + x[2]

    def distance_heuristic(self, succ):
        return distance_to_bucharest[succ]


# A estrella
def a_star(problem):
    l = [(problem.initial, [], 0)]
    closed = []
    while l:
        node, actions, cost = l.pop()
        closed += [node]
        if problem.goal_test(node):
            return node, actions, cost

        for succ, action, cost_ in problem.actions(node):
            # Chequeamos los ancestros
            if succ not in closed:
                l += [(succ, actions + [action], cost + cost_)]
        
        l.sort(key=problem.heuristic, reverse=True)

if __name__ == "__main__":
    problem = searchCity("Arad", "Bucharest", 0)
    _, actions, cost = a_star(problem)
    print("Heuristica a: " + str(actions), "Costo: " + str(cost))
    problem = searchCity("Arad", "Bucharest", 1)
    _, actions, cost = a_star(problem)
    print("Heuristica b: " + str(actions), "Costo: " + str(cost))
    problem = searchCity("Arad", "Bucharest", 2)
    _, actions, cost = a_star(problem)
    print("Heuristica c: " + str(actions), "Costo: " + str(cost))
