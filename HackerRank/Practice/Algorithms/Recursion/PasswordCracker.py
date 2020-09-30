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


def main():
    T = int(input())
    for _ in range(T):
        N = int(input())
        words = list(input().split())
        S = input()

        dp = [0] * (len(S) + 1)
        dp[0] = 1
        prev = [(-1, "")] * (len(S) + 1)

        for i in range(len(S)):
            if dp[i]:
                for word in words:
                    if S[i:i+len(word)] == word:
                        dp[i + len(word)] = 1
                        prev[i + len(word)] = (i, word)

        if dp[len(S)] == 0:
            print("WRONG PASSWORD")
        else:
            now = len(S)
            ans = []
            while now > 0:
                ans.append(prev[now][1])
                now = prev[now][0]
            print(*ans[::-1])


if __name__ == '__main__':
    main()
