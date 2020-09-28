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


N, M, Q = 0, 0, 0
A, B, C, D = [0], [0], [0], [0]
ans = 0

def dfs(i, l):
    global ans, N, M, Q, A, B, C, D
    if i >= N:
        tmp = 0
        for j in range(Q):
            if l[B[j]] - l[A[j]] == C[j]:
                tmp += D[j]
        ans = max(ans, tmp)
        return

    for j in range(1, M + 1):
        if l:
            if j >= l[-1]:
                l.append(j)
                dfs(i + 1, l)
                l.pop()
        else:
            l.append(j)
            dfs(i + 1, l)
            l.pop()


def solve():
    global ans, N, M, Q, A, B, C, D
    N, M, Q = map(int, input().split())
    A, B, C, D = [0] * Q, [0] * Q, [0] * Q, [0] * Q
    for i in range(Q):
        A[i], B[i], C[i], D[i] = map(int, input().split())
        A[i] -= 1
        B[i] -= 1

    l = []
    dfs(0, l)
    print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
