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
    H = [[False] * N for _ in range(N)]
    G = [[False] * N for _ in range(N)]
    M1 = int(input())
    for _ in range(M1):
        U, V = map(int, input().split())
        U -= 1
        V -= 1
        H[U][V] = H[V][U] = True
    M2 = int(input())
    for _ in range(M2):
        U, V = map(int, input().split())
        U -= 1
        V -= 1
        G[U][V] = G[V][U] = True

    A = [[0] * N for _ in range(N)]
    for i in range(N - 1):
        l = list(map(int, input().split()))
        for j in range(N - i - 1):
            A[i][i + 1 + j] = A[i + 1 + j][i] = l[j]

    ans = INF
    for p in permutations(range(N)):
        a = 0
        for u in range(N):
            for v in range(u + 1, N):
                if H[u][v] and not G[p[u]][p[v]]:
                    a += A[p[u]][p[v]]
                if not H[u][v] and G[p[u]][p[v]]:
                    a += A[p[u]][p[v]]
        ans = min(ans, a)

    print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
