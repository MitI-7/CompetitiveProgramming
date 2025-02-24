#!/usr/bin/env python3
import os
import random
import sys
import time
from bisect import bisect, bisect_left, bisect_right
from collections import defaultdict, Counter, deque
from functools import lru_cache
from itertools import product, groupby, count, permutations, combinations
from math import pi, sqrt
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
    if b == 0:
        return bit & ~(1 << i)
    else:
        return bit | (1 << i)


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


def main():
    N = int(input())

    points = []
    for _ in range(N):
        X, Y = map(int, input().split())
        points.append((X, Y))

    ans = []
    for (i, (x1, y1)) in enumerate(points):
        best = None
        far = 0
        for (j, (x2, y2)) in enumerate(points):
            if i == j:
                continue

            if (x1 - x2) ** 2 + (y1 - y2) ** 2 > far:
                far = (x1 - x2) ** 2 + (y1 - y2) ** 2
                best = j
        ans.append(best + 1)

    print(*ans)


if __name__ == '__main__':
    main()
