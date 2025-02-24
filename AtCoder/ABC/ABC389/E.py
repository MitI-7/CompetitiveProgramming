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


def solve(M, P):
    def ok(x):
        m = 0
        num = 0
        for p in P:
            k = (x + p) // (2 * p)
            m += k * k * p
            num += k
        return m, num

    left, right = 0, 1 << 62
    ans = 0
    while right - left > 1:
        mid = (left + right) // 2
        need, num = ok(mid)
        if need <= M:
            left = mid
            ans = num
        else:
            right = mid

    tmp = 0
    num = 0
    for p in P:
        k = (right + p) // (2 * p)
        if (2 * k - 1) * p == right:
            num += 1
            k -= 1
        M -= k * k * p
        tmp += k
    tmp += min(M // right, num)

    if M >= 0:
        ans = max(ans, tmp)

    return ans

def main():
    N, M = map(int, input().split())
    P = list(map(int, input().split()))
    P.sort()
    print(solve(M, P))


if __name__ == '__main__':
    main()
