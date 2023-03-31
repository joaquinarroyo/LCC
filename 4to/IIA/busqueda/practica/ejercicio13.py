def solve(queens):
    # Encontrar la siguiente creina sin columna asignada
    row = None
    for i_ in range(0, len(queens)):
        if queens[i_] == -1:
            row = i_
            break

    # Si no hay más reinas sin columna asignada
    if row is None:
        return True

    for col in range(0, len(queens)):
        # Si el número es válido
        if is_valid(queens, row, col):
            # Asignar el número de columna a la reina
            queens[row] = col

            # Llamar recursivamente a la función
            if solve(queens):
                return True

            # Si no se puede resolver con la columna actual, retroceder y probar otra columna
            queens[row] = -1

    # Si no se puede resolver con ninguna columna, el tablero no tiene solución
    return False


def is_valid(queens, row, col):
    if col in queens:
        return False

    for i in range(row):
        if abs(i - row) == abs(queens[i] - col):
            return False
    return True


if __name__ == '__main__':
    n = 9
    queens = n*[-1]
    board = [[0 for _ in range(n)] for _ in range(n)]
    solve(queens)
    print(queens)
    print("board")
    for i in range(n):
        board[queens[i]][i] = 1
    for row in board:
        print(row)
