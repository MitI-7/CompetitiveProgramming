from collections import defaultdict, Counter
from itertools import product, groupby, count, permutations, combinations
from math import pi, sqrt
from collections import deque
from bisect import bisect, bisect_left, bisect_right
from string import ascii_lowercase
from functools import lru_cache
import sys

sys.setrecursionlimit(100000000)

INF = float("inf")
YES, Yes, yes, NO, No, no = "YES", "Yes", "yes", "NO", "No", "no"
dy4, dx4 = [0, 1, 0, -1], [1, 0, -1, 0]
dy8, dx8 = [0, -1, 0, 1, 1, -1, -1, 1], [1, 0, -1, 0, 1, 1, -1, -1]


def inside(y, x, H, W):
    return 0 <= y < H and 0 <= x < W


def ceil(a, b):
    return (a + b - 1) // b


# 初項s, 交差dのn個の数列の和
def sum_of_arithmetic_progression(s, d, n):
    return n * (2 * s + (n - 1) * d) // 2


# aとbの最大公約数
def gcd(a, b):
    if b == 0:
        return a
    return gcd(b, a % b)


# aとbの最小公倍数
def lcm(a, b):
    g = gcd(a, b)
    return a / g * b


def l(v):
    v1 = v[::]
    for i in range(len(v)):
        v1[i] += v[i - 1]
    return v1


def main():
    N = int(input())
    d = defaultdict(list)
    for _ in range(N):
        s = input()
        d[len(s)].append(s)

    for k, v in d.items():
        print(*sorted(v), sep="\n")


if __name__ == '__main__':
    main()
