#!/usr/bin/env python3
from collections import defaultdict, Counter
from itertools import product, groupby, count, permutations, combinations
from math import pi, sqrt
from collections import deque
from bisect import bisect, bisect_left, bisect_right
from string import ascii_lowercase
from functools import lru_cache
import sys
sys.setrecursionlimit(500000)
INF = float("inf")
YES, Yes, yes, NO, No, no = "YES", "Yes", "yes", "NO", "No", "no"
dy4, dx4 = [0, 1, 0, -1], [1, 0, -1, 0]                                 # 右，上，左，下
dy8, dx8 = [0, -1, 0, 1, 1, -1, -1, 1], [1, 0, -1, 0, 1, 1, -1, -1]     # 右，下，左，上，右上，右下，左下，左上

# memo
# print(f"0埋めで10桁表示: {123:010}")
# print(f"小数点以下2桁を表示: {123.456:.2f}")


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
    return a // g * b


def solve():
    N, M = map(int, input().split())

    switch_light = [list() for _ in range(N)]
    for i in range(M):
        l = list(map(int, input().split()))
        for j in range(1, len(l)):
            switch_light[l[j] - 1].append(i)

    P = list(map(int, input().split()))

    ans = 0
    for b in range(2**N):
        count = [0] * M
        for i in range(N):
            if (b >> i) & 1:
                for j in switch_light[i]:
                    count[j] = (count[j] + 1) % 2
        ans += (count == P)

    print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
