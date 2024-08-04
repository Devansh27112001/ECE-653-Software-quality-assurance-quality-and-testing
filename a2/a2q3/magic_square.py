'''Magic Square

https://en.wikipedia.org/wiki/Magic_square

A magic square is a n * n square grid filled with distinct positive integers in
the range 1, 2, ..., n^2 such that each cell contains a different integer and
the sum of the integers in each row, column, and diagonal is equal.

'''

from z3 import *


def solve_magic_square(n, r, c, val):
    solver = Solver()
    # CREATE CONSTRAINTS AND LOAD STORE THEM IN THE SOLVER
    sum_square = (1 + n * n) * (n) / (2)
    conditions = []
    num = [[0] * n for _ in range(n)]

    for i in range(n):
        row = 0
        for j in range(n):
            num[i][j] = FreshInt('x')
            conditions.append(1 <= num[i][j])
            conditions.append(num[i][j] <= n * n)
            row += num[i][j]
        conditions.append(row == sum_square)
    
    for i in range(n):
        column = 0
        for j in range(n):
            column += num[j][i]
        conditions.append(column == sum_square)


    d1 = 0
    d2 = 0

    for i in range(n):
        d1 += num[i][i]
        d2 += num[i][n - i - 1]
    conditions.append(d1 == sum_square)
    conditions.append(d2 == sum_square)
    conditions.append(num[r][c] == val)

    solver.add(Distinct([num[i][j] for i in range(n) for j in range(n)]))
    solver.add(conditions)

    if solver.check() == sat:
        mod = solver.model()
        res = [[0] * n for _ in range(n)]

        # CREATE RESULT MAGIC SQUARE BASED ON THE MODEL FROM THE SOLVER
        for i in range(n):
            for j in range(n):
                res[i][j] = mod.eval(num[i][j]).as_long()


        return res
    else:
        return None


def print_square(square):
    '''
    Prints a magic square as a square on the console
    '''
    n = len(square)

    assert n > 0
    for i in range(n):
        assert len(square[i]) == n

    for i in range(n):
        line = []
        for j in range(n):
            line.append(str(square[i][j]))
        print('\t'.join(line))


def puzzle(n, r, c, val):
    res = solve_magic_square(n, r, c, val)
    if res is None:
        print('No solution!')
    else:
        print('Solution:')
        print_square(res)


if __name__ == '__main__':
    n = 3 
    r = 1
    c = 1
    val = 5
    puzzle(n, r, c, val)
