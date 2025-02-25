"""
    Script for making a animation of one fire
    It reads the fire data from standard input in the format that
    `fire_animation_data` prints them

    Usage:
    python fire_animation.py [output_filename]
"""

import sys
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.animation as animation

from typing import List, Tuple


def animate_fire(width: int, height: int, steps: List[List[Tuple[int, int]]]) -> animation.ArtistAnimation:
    """
    Animates the fire spread
    Each element of steps is a list of coordinates of burning cells in that step

    The burning cells in each step are plotted in red
    The already burned cells are plotted in black
    The rest of the cells are plotted in green
    """

    burned_cells_steps = np.full((width, height), -1)
    for i, step in enumerate(steps):
        for x, y in step:
            burned_cells_steps[x, y] = i

    fig = plt.figure()
    images = []
    for i in range(len(steps) + 1):
        burned_cells = np.zeros((width, height, 3))
        for x in range(width):
            for y in range(height):
                if burned_cells_steps[x, y] == -1 or burned_cells_steps[x, y] > i:
                    # Color green in rgb
                    burned_cells[x, y] = [0, 1, 0]
                elif burned_cells_steps[x, y] < i:
                    # Color black in rgb
                    burned_cells[x, y] = [0, 0, 0]
                elif burned_cells_steps[x, y] == i:
                    # Color red in rgb
                    burned_cells[x, y] = [1, 0, 0]
        im = plt.imshow(burned_cells)
        images.append([im])

    anim = animation.ArtistAnimation(fig, images)
    return anim


def read_fire() -> Tuple[int, int, List[List[Tuple[int, int]]]]:
    """
    Reads the fire from standard input
    Example input:
    Landscape size: 5 5
    Step 1:
    0 0
    Step 2:
    0 1
    1 0
    Step 3:
    0 2
    1 2
    1 1
    """
    _, _, width, height = input().split()
    width, height = int(width), int(height)
    steps: List[List[Tuple[int, int]]] = []
    while True:
        try:
            line: str = input()
        except EOFError:
            break
        if line == "":
            break
        elif line[0:5] == "Step ":
            steps.append([])
        else:
            x, y = line.split()
            steps[-1].append((int(x), int(y)))
    return width, height, steps


def main():
    # Get command line argument
    output_filename: str = "fire.mp4"
    if len(sys.argv) > 1:
        output_filename = sys.argv[1]
    width, height, steps = read_fire()
    anim = animate_fire(width, height, steps)
    anim.save(output_filename, fps=5)


if __name__ == "__main__":
    main()
