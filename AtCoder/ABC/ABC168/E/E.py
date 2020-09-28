#!/usr/bin/env python3
from collections import defaultdict, Counter
from itertools import product, groupby, count, permutations, combinations
from math import pi, sqrt
from collections import deque
from bisect import bisect, bisect_left, bisect_right
from string import ascii_lowercase
from functools import lru_cache
from fractions import Fraction
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


MOD = 1000000007


def func(v1, v2):
    ans = 1
    ans += pow(2, v1, MOD) - 1
    ans += pow(2, v2, MOD) - 1

    return ans % MOD


def solve():
    N = int(input())

    num_zero = 0

    d = defaultdict(lambda: [0, 0])
    for _ in range(N):
        A, B = map(int, input().split())
        if A == 0 and B == 0:
            num_zero += 1
            continue
        elif A == 0:
            d[(0, 0)][0] += 1
        elif B == 0:
            d[(0, 0)][1] += 1
        else:
            g = gcd(abs(A), abs(B))
            A //= g
            B //= g
            if B > 0:
                if A > 0:
                    d[(A, B)][1] += 1
                else:
                    d[(B, -A)][0] += 1
            else:
                if A < 0:
                    d[(-A, -B)][1] += 1
                else:
                    d[(-B, A)][0] += 1

    ans = 1
    for k, v in d.items():
        ans *= func(v[0], v[1])
        ans %= MOD

    print((ans + num_zero + MOD - 1) % MOD)


def main():
    solve()


if __name__ == '__main__':
    main()
