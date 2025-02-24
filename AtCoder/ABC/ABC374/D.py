import random
import sys
from bisect import bisect, bisect_left, bisect_right
from collections import Counter, defaultdict, deque
from functools import lru_cache
from itertools import combinations, count, groupby, permutations, product
from math import gcd, lcm, pi, sqrt
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
    return bit & ~(1 << i) if b == 0 else bit | (1 << i)


def inside(y, x, H, W):
    return 0 <= y < H and 0 <= x < W


def ceil(a, b):
    return (a + b - 1) // b


def euclid(x1, y1, x2, y2):
    return sqrt(abs(x1 - x2) ** 2 + abs(y1 - y2) ** 2)


def solve():
    N, S, T = map(int, input().split())

    points = []
    for _ in range(N):
        A, B, C, D = map(int, input().split())
        points.append((A, B, C, D))

    ans = INF
    for p in permutations(points):
        for bit in range(1 << N):
            t = 0.0
            now = (0, 0)
            for i in range(N):
                a, b, c, d = p[i]
                if is_bit_on(bit, i):
                    t += euclid(now[0], now[1], a, b) / S
                    t += euclid(a, b, c, d) / T
                    now = (c, d)
                else:
                    t += euclid(now[0], now[1], c, d) / S
                    t += euclid(a, b, c, d) / T
                    now = (a, b)
            ans = min(ans, t)

    print(f"{ans:.8f}")


def main():
    solve()


if __name__ == '__main__':
    main()
