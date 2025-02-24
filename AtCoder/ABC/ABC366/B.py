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


def matrix_rotate(A):
    H, W = len(A), len(A[0])
    for a in A:
        W = max(W, len(a))
    ans = [[None] * H for _ in range(W)]

    for y in range(H):
        for x in range(W):
            if x < len(A[y]):
                ans[x][-y - 1] = A[y][x]
            else:
                ans[x][-y - 1] = '*'

    return ans


def solve():
    N = int(input())
    S = [input() for _ in range(N)]

    ans = matrix_rotate(S)
    for a in ans:
        print("".join(a).rstrip("*"))


def main():
    solve()


if __name__ == '__main__':
    main()
