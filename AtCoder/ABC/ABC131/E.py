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


def solve(N, K):
    num_pair = (N - 1) * (N - 2) // 2

    if num_pair < K:
        return None

    ans = []
    # うにをつくる
    for i in range(1, N):
        ans.append((0, i))

    if num_pair == K:
        return ans

    # うにのとげ同士に辺をはっていく
    for i in range(1, N):
        for j in range(i + 1, N):
            ans.append((i, j))
            num_pair -= 1
            if num_pair == K:
                return ans


def main():
    N, K = map(int, input().split())
    ans = solve(N, K)
    if ans is None:
        print(-1)
    else:
        print(len(ans))
        for u, v in ans:
            print(u + 1, v + 1)


if __name__ == '__main__':
    main()
