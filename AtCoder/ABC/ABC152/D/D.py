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


def dfs(d, tight, str_N, pre):
    if d >= len(str_N) - 1:
        if int(pre) <= int(str_N[-1]):
            return 1
        else:
            return int(not tight)

    ans = 0
    if tight:
        for i in range(0, int(str_N[d]) + 1):
            ans += dfs(d + 1, str(i) == str_N[d], str_N, pre)
    else:
        for i in range(0, 10):
            ans += dfs(d + 1, False, str_N, pre)

    return ans


def solve():
    N = int(input())
    str_N = str(N)
    D = len(str_N)

    memo = [-1] * 10
    ans = 0
    for A in range(1, N + 1):
        a = str(A)
        pre = a[0]
        post = a[-1]

        if pre == "0" or post == "0":
            continue

        for d in range(1, D + 1):
            if d == 1:
                if pre == post:
                    ans += 1
            elif d != D:
                ans += 10 ** (d - 2)
            else:
                # B = post, xxx, pre
                if post == str(N)[0]:
                    if memo[int(pre)] == -1:
                        memo[int(pre)] = dfs(1, True, str_N, pre)
                    ans += memo[int(pre)]
                elif int(post) < int(str_N[0]):
                    ans += 10 ** (d - 2)

    print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
