"""
    Script for drawing the burned probabilities
    It reads the burned amounts from standard input in the format that
    `burned_probabilities_data` prints them

    Usage:
    python draw_burned_probabilities.py [output_filename]
"""

import sys
import numpy as np
import matplotlib.pyplot as plt
from typing import Tuple

FILENAME = "./graphics/simdata/burned_probabilities_data.txt"
DIR = "./outputs/"

def read_burned_amounts() -> Tuple[int, np.ndarray]:
    """
    Reads the burned amounts from standard input
    Example input:
    Landscape size: 5 5
    Simulations: 100
    53 81 81 72 49
    66 100 86 79 68
    73 84 85 77 66
    74 82 79 73 0
    64 75 64 55 0
    """
    with open(FILENAME, "r") as file:
        lines = file.readlines()
        _, _, width, height = lines.pop(0).split()
        width, height = int(width), int(height)
        _, simulations = lines.pop(0).split()
        simulations = int(simulations)
        burned_amounts = np.zeros((width, height), dtype=int)
        for j in range(height):
            line = lines[j].split()
            for i, amount in enumerate(line):
                burned_amounts[i, j] = int(amount)

    return simulations, burned_amounts

def draw_burned_probabilities(simulations: int, burned_amounts: np.ndarray, output_filename: str):
    """
    Generates a plot of the burned probabilities
    Colors:
    - Red: 100% probability
    - Green: 0% probability
    """
    burned_probabilities = burned_amounts / simulations
    im = plt.imshow(burned_probabilities)
    plt.colorbar(im)
    plt.savefig(output_filename)

def main():
    output_filename: str = "burned_probabilities.png"
    if len(sys.argv) > 1:
        output_filename = sys.argv[1]
    simulations, burned_amounts = read_burned_amounts()
    draw_burned_probabilities(simulations, burned_amounts, f"{DIR}{output_filename}")

if __name__ == "__main__":
    main()
