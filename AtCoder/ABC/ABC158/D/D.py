#!/usr/bin/env python3
from collections import defaultdict, Counter
from itertools import product, groupby, count, permutations, combinations
from math import pi, sqrt
from collections import deque
from bisect import bisect, bisect_left, bisect_right
from string import ascii_lowercase
from functools import lru_cache
import sys
sys.setrecursionlimit(10000)
INF = float("inf")
YES, Yes, yes, NO, No, no = "YES", "Yes", "yes", "NO", "No", "no"
dy4, dx4 = [0, 1, 0, -1], [1, 0, -1, 0]
dy8, dx8 = [0, -1, 0, 1, 1, -1, -1, 1], [1, 0, -1, 0, 1, 1, -1, -1]


def inside(y, x, H, W):
    return 0 <= y < H and 0 <= x < W


def ceil(a, b):
    return (a + b - 1) // b


def sum_of_arithmetic_progression(s, d, n):
    return n * (2 * s + (n - 1) * d) // 2


def gcd(a, b):
    if b == 0:
        return a
    return gcd(b, a % b)


def lcm(a, b):
    g = gcd(a, b)
    return a / g * b


def solve():
    S = input()
    Q = int(input())

    que = deque(S)

    rev = False
    for _ in range(Q):
        T = input()

        if len(T) == 1:
            rev = not rev
        else:
            t, F, C = T.split()
            # 先頭
            if int(F) == 1:
                if not rev:
                    que.appendleft(C)
                else:
                    que.append(C)
            # 末尾
            else:
                if not rev:
                    que.append(C)
                else:
                    que.appendleft(C)

    if rev:
        que = reversed(que)
    print(*que, sep="")


def main():
    solve()


if __name__ == '__main__':
    main()
