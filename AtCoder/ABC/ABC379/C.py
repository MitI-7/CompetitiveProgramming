import math
import random
import sys
from bisect import bisect, bisect_left, bisect_right
from collections import Counter, defaultdict, deque
from functools import lru_cache
from itertools import combinations, count, groupby, permutations, product
from math import gcd, lcm, pi, sqrt
from string import ascii_lowercase, ascii_uppercase

sys.setrecursionlimit(500000)
INF = float("inf")
YES, Yes, yes, NO, No, no = "YES", "Yes", "yes", "NO", "No", "no"
dy4, dx4 = [0, 1, 0, -1], [1, 0, -1, 0]  # 右，上，左，下
dy8, dx8 = [0, -1, 0, 1, 1, -1, -1, 1], [1, 0, -1, 0, 1, 1, -1, -1]  # 右，下，左，上，右上，右下，左下，左上


# memo
# print(f"0埋めで10桁表示: {123:010}")
# print(f"小数点以下2桁を表示: {123.456:.2f}")

def is_bit_on(bit, i):
    return (bit >> i) & 1


def get_bit_set(bit, i, b):
    assert (b == 0 or b == 1)
    return bit & ~(1 << i) if b == 0 else bit | (1 << i)


def inside(y, x, H, W):
    return 0 <= y < H and 0 <= x < W


def ceil(a, b):
    return (a + b - 1) // b


def f(n):
    if n <= 1:
        return 0
    n -= 1
    return (1 + n) * n // 2


def solve():
    N, M = map(int, input().split())
    X = list(map(int, input().split()))
    A = list(map(int, input().split()))

    if sum(A) != N:
        print(-1)
        return

    xa = []
    for i in range(M):
        xa.append([X[i], A[i]])
    xa.sort()

    if xa[-1][0] != N:
        xa.append([N, 0])
        M += 1

    ans = 0
    for i in range(M - 1):
        x, a = xa[i]
        next_x = xa[i + 1][0]
        d = next_x - x
        if d >= a:
            ans += f(a)
        else:
            ans += f(d) + (a - d) * d
            xa[i + 1][1] += a - d

    if xa[-1][1] != 1:
        print(-1)
    else:
        print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
