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
    S = input()
    N = len(S)
    ans = [0] * N

    # R を右に送っていく
    num_r = 0
    for i in range(N):
        if S[i] == 'R':
            num_r += 1
        if S[i] == 'L':
            # RLがみつかった
            ans[i] += num_r // 2
            ans[i - 1] += (num_r + 1) // 2
            num_r = 0

    # L を左に送っていく
    num_l = 0
    for i in range(N - 1, -1, -1):
        if S[i] == 'L':
            num_l += 1
        if S[i] == 'R':
            # RLがみつかった
            ans[i] += num_l // 2
            ans[i + 1] += (num_l + 1) // 2
            num_l = 0

    print(*ans)


def main():
    solve()


if __name__ == '__main__':
    main()
