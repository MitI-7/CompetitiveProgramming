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


class BisectWrapper:
    try:
        from typing import List
    except:
        List = list

    def __init__(self):
        pass

    # aにxが存在するか
    @staticmethod
    def exist(a: List, x: int):
        i = bisect_left(a, x)
        if i != len(a) and a[i] == x:
            return True
        return False

    # xのindex(なければ-1)
    @staticmethod
    def index(a: List, x: int):
        i = bisect_left(a, x)
        if i != len(a) and a[i] == x:
            return i
        return -1

    # y < xのようなyの中でもっとも右のindex
    @staticmethod
    def index_lt(a: List, x: int):
        i = bisect_left(a, x)
        if i:
            return i - 1
        return -1

    # y < xのようなyの個数
    @staticmethod
    def num_lt(a: List, x: int):
        return bisect_left(a, x)

    # y <= xのようなyの中でもっとも右のindex
    @staticmethod
    def index_lte(a: List, x: int):
        i = bisect_right(a, x)
        if i:
            return i - 1
        return -1

    # y < xのようなyの個数
    @staticmethod
    def num_lte(a: List, x: int):
        return bisect_right(a, x)

    # y > xのようなyの中でもっとも左のindex
    @staticmethod
    def index_gt(a: List, x: int):
        i = bisect_right(a, x)
        if i != len(a):
            return i
        return -1

    # y > xのようなyの個数
    @staticmethod
    def num_gt(a: List, x: int):
        return len(a) - bisect_right(a, x)

    # y >= xのようなyの中でもっとも左のindex
    @staticmethod
    def index_gte(a: List, x: int):
        i = bisect_left(a, x)
        if i != len(a):
            return i
        return -1

    # y >= xのようなyの個数
    @staticmethod
    def num_gte(a: List, x: int):
        return len(a) - bisect_left(a, x)


def solve():
    N = int(input())
    A = list(map(int, input().split()))

    ans = 0
    for a in A:
        ans += BisectWrapper.num_gte(A, a * 2)
    print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
