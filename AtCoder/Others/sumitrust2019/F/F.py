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


def meet(diff, T1, T2, A1, A2, B1, B2):
    ans = 0
    pre_diff = diff
    a = T1 * A1
    b = T1 * B1

    diff += a
    diff -= b

    if (pre_diff * diff) < 0 or (pre_diff != 0 and diff == 0):
        ans += 1

    pre_diff = diff
    a = T2 * A2
    b = T2 * B2

    diff += a
    diff -= b

    if (pre_diff * diff) < 0 or (pre_diff != 0 and diff == 0):
        ans += 1

    return ans


def solve():
    T1, T2 = map(int, input().split())
    A1, A2 = map(int, input().split())
    B1, B2 = map(int, input().split())

    # 無限回
    if (T1 * A1 + T2 * A2) == (T1 * B1 + T2 * B2):
        print("infinity")
        return

    # 0回
    if (A1 > B1 and A2 > B2) or (A1 < B1 and A2 < B2):
        print(0)
        return

    one_diff = (T1 * A1 + T2 * A2) - (T1 * B1 + T2 * B2)

    ans = 0
    diff = 0
    for i in range(100):
        num = meet(diff, T1, T2, A1, A2, B1, B2)
        if num == 0:
            break
        ans += num
        diff += one_diff

    left = -1
    right = 10**20
    while right - left > 1:
        m = (right + left) // 2
        tmp = diff + m * one_diff
        if meet(tmp, T1, T2, A1, A2, B1, B2):
            left = m
        else:
            right = m

    x = max(0, left - 10)
    ans += meet(diff, T1, T2, A1, A2, B1, B2) * x
    diff += one_diff * x

    for i in range(100):
        num = meet(diff, T1, T2, A1, A2, B1, B2)
        if num == 0:
            break
        ans += num
        diff += one_diff

    print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
