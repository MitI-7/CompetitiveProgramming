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


# 2次元行列を右に90度回転
def rotate(A):
    H, W = len(A), len(A[0])
    ans = [[None] * H for _ in range(W)]

    for y in range(H):
        for x in range(W):
            ans[W - 1 - x][y] = A[y][x]

    return ans


def solve():
    N = int(input())
    A = []
    for _ in range(N):
        A.append(list(map(int, input().split())))
    B = []
    for _ in range(N):
        B.append(list(map(int, input().split())))

    for i in range(4):
        ok = True
        for y in range(N):
            for x in range(N):
                if A[y][x] == 1:
                    ok &= B[y][x] == 1
        if ok:
            print("Yes")
            return
        A = rotate(A)

    print("No")


def main():
    solve()


if __name__ == '__main__':
    main()
