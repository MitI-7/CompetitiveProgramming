import itertools
import math
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


def main():
    H, W = map(int, input().split())
    grid = []
    for _ in range(H):
        grid.append(input())

    y1, x1, y2, x2 = INF, INF, -INF, -INF
    for y in range(H):
        for x in range(W):
            if grid[y][x] == '#':
                y1 = min(y1, y)
                x1 = min(x1, x)
                y2 = max(y2, y)
                x2 = max(x2, x)

    for y in range(H):
        for x in range(W):
            if y1 <= y <= y2 and x1 <= x <= x2 and grid[y][x] == '.':
                print(No)
                return
    print(Yes)


if __name__ == '__main__':
    main()
