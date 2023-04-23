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
dy4, dx4 = [0, 1, 0, -1], [1, 0, -1, 0]  # 右，上，左，下
dy8, dx8 = [0, -1, 0, 1, 1, -1, -1, 1], [1, 0, -1, 0, 1, 1, -1, -1]  # 右，下，左，上，右上，右下，左下，左上


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


# 多角形が凸かどうか判定する
# vertex_list: 反時計回りで並んだ頂点のリスト
def is_convex(vertex_list):
    # 外積
    def cross(x1, y1, x2, y2):
        return x1 * y2 - x2 * y1

    n = len(vertex_list)
    for i in range(n):
        a = vertex_list[i % n]
        b = vertex_list[(i + 1) % n]
        c = vertex_list[(i + 2) % n]

        ab = [b[0] - a[0], b[1] - a[1]]
        bc = [c[0] - b[0], c[1] - b[1]]

        if cross(*ab, *bc) < 0:
            return False

    return True


def solve():
    A = list(map(int, input().split()))
    B = list(map(int, input().split()))
    C = list(map(int, input().split()))
    D = list(map(int, input().split()))

    if is_convex([A, B, C, D]):
        print("Yes")
    else:
        print("No")


def main():
    solve()


if __name__ == '__main__':
    main()
