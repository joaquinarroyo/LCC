
sudoku = [
    [5, 0, 4, 6, 7, 8, 9, 1, 2],
    [6, 7, 2, 1, 9, 5, 3, 4, 8],
    [1, 9, 8, 0, 4, 0, 5, 6, 7],
    [8, 5, 9, 7, 6, 0, 4, 2, 3],
    [4, 2, 6, 8, 5, 0, 7, 9, 1],
    [7, 1, 0, 9, 2, 0, 8, 5, 6],
    [9, 6, 1, 0, 3, 0, 2, 8, 4],
    [2, 8, 7, 4, 1, 0, 6, 3, 5],
    [3, 4, 5, 2, 8, 0, 1, 7, 9]
]


def solve_sudoku(board):
    # Encontrar la siguiente celda vacía en el tablero
    row, col = find_empty_cell(board)

    # Si no hay más celdas vacías, el tablero está resuelto
    if row is None:
        return True

    # Probar con cada número del 1 al 9 en la celda vacía
    for num in range(1, 10):
        # Si el número es válido en la celda vacía
        if is_valid(board, row, col, num):
            # Asignar el número a la celda
            board[row][col] = num

            # Llamar recursivamente a la función para resolver el resto del tablero
            if solve_sudoku(board):
                return True

            # Si no se puede resolver con el número actual, retroceder y probar otro número
            board[row][col] = 0

    # Si no se puede resolver con ningún número, el tablero no tiene solución
    return False


def find_empty_cell(board):
    for row in range(9):
        for col in range(9):
            if board[row][col] == 0:
                return row, col
    return None, None


def is_valid(board, row, col, num):
    # Verificar fila
    if num in board[row]:
        return False

    # Verificar columna
    if num in [board[i][col] for i in range(9)]:
        return False

    # Verificar subcuadrícula
    sub_row, sub_col = (row // 3) * 3, (col // 3) * 3
    for i in range(sub_row, sub_row + 3):
        for j in range(sub_col, sub_col + 3):
            if board[i][j] == num:
                return False

    # Si todas las verificaciones son correctas, el número es válido
    return True


if __name__ == '__main__':
    solve_sudoku(sudoku)
    for row in sudoku:
        print(row)
