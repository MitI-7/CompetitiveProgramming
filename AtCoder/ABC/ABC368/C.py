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


def solve():
    N = int(input())
    H = list(map(int, input().split()))[::-1]

    ans = 0
    T = 0
    while H:
        while T != 0 and H[-1] > 0:
            if T == 2:
                H[-1] -= 3
            else:
                H[-1] -= 1
            T = (T + 1) % 3
            ans += 1

        if H[-1] >= 5:
            num = H[-1] // 5
            ans += num * 3
            H[-1] -= 5 * num

        while H[-1] > 0:
            if T == 2:
                H[-1] -= 3
            else:
                H[-1] -= 1
            T = (T + 1) % 3
            ans += 1

        assert H[-1] <= 0
        H.pop()

    print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
