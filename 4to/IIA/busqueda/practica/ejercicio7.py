
class Robot:
    def __init__(self, orientation, x, y, map):
        self.orientation = orientation
        self.x = x
        self.y = y
        self.map = map

    def get_position(self):
        return (self.x, self.y)

    def move(self):
        max_x = len(self.map[0])
        max_y = len(self.map)
        if self.orientation == "N":
            if self.y > 0 and self.map[self.y - 1][self.x] != 1:
                self.y -= 1
        elif self.orientation == "E":
            if self.x < max_x - 1 and self.map[self.y][self.x + 1] != 1:
                self.x += 1
        elif self.orientation == "S":
            if self.y < max_y - 1 and self.map[self.y + 1][self.x] != 1:
                self.y += 1
        elif self.orientation == "W":
            if self.x > 0 and self.map[self.y][self.x - 1] != 1:
                self.x -= 1
        return self.get_position()
    
    def rotate(self, orientation):
        self.orientation = orientation
    
    def posible_rotations(self):
        if self.orientation == "N":
            return ["E", "W"]
        elif self.orientation == "E":
            return ["S", "N"]
        elif self.orientation == "S":
            return ["W", "E"]
        elif self.orientation == "W":
            return ["N", "S"]
    
    def posible_moves(self):
        max_x = len(self.map[0])
        max_y = len(self.map)
        moves = []
        if self.orientation == "N":
            if self.y > 0 and self.map[self.y - 1][self.x] != 1:
                moves += [(self.x, self.y - 1)]
        elif self.orientation == "E":
            if self.x < max_x - 1 and self.map[self.y][self.x + 1] != 1:
                moves += [(self.x + 1, self.y)]
        elif self.orientation == "S":
            if self.y < max_y - 1 and self.map[self.y + 1][self.x] != 1:
                moves += [(self.x, self.y + 1)]
        elif self.orientation == "W":
            if self.x > 0 and self.map[self.y][self.x - 1] != 1:
                moves += [(self.x - 1, self.y)]
        return moves

    def __str__(self):
        return "Robot: " + str(self.get_position()) + " " + self.orientation
    
    def copy(self):
        return Robot(self.orientation, self.x, self.y, self.map)

class Problem:
    def __init__(self, robot, goal):
        self.robot = robot
        self.goal = goal

    def set_robot(self, robot):
        self.robot = robot

    def cost(self, action):
        if action[1] == "M":
            return 2
        else:
            return 1

    def actions(self):
        actions = []
        for orientation in self.robot.posible_rotations():
            robot = self.robot.copy()
            robot.rotate(orientation)
            actions += [(robot, (orientation, "R"), 1)]
        for position in self.robot.posible_moves():
            robot = self.robot.copy()
            robot.move()
            actions += [(robot, (position, "M"), 2)]
        return actions

    def goal_test(self, state):
        return state.get_position() == self.goal
    
# A estrella
def a_star(problem):
    frontier = [(problem.robot, [], 0)]
    closed = []
    while frontier:
        node, actions, cost = frontier.pop()
        problem.set_robot(node)
        closed += [(node.get_position(), node.orientation)]
        if problem.goal_test(node):
            return node, actions, cost

        for succ, action, cost_ in problem.actions():
            # Chequeamos los ancestros
            if (succ.get_position(), succ.orientation) not in closed:
                frontier += [(succ, actions + [action], cost + cost_)]
        frontier.sort(key=lambda x: x[2], reverse=True)

if __name__ == "__main__":
    # 5x5
    map_ = [
        [0, 0, 0, 0, 0],
        [1, 0, 1, 1, 0],
        [0, 0, 0, 0, 0],
        [1, 0, 1, 1, 1],
        [0, 0, 0, 0, 0]
    ]

    start_x, start_y = 4, 4
    start_orientation = "N"
    robot = Robot(start_orientation, start_x, start_y, map_)
    goal = (0, 0)
    problem = Problem(robot, goal)
    _, actions, cost = a_star(problem)
    print(actions, "Costo:", cost)
