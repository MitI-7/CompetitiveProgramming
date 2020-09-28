#!/usr/bin/env python3
from collections import defaultdict, Counter
from itertools import product, groupby, count, permutations, combinations
from math import pi, sqrt
from collections import deque
from bisect import bisect, bisect_left, bisect_right
from string import ascii_lowercase
from functools import lru_cache
import sys
sys.setrecursionlimit(10000)
INF = float("inf")
YES, Yes, yes, NO, No, no = "YES", "Yes", "yes", "NO", "No", "no"
dy4, dx4 = [0, 1, 0, -1], [1, 0, -1, 0]
dy8, dx8 = [0, -1, 0, 1, 1, -1, -1, 1], [1, 0, -1, 0, 1, 1, -1, -1]


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
    return a / g * b


def solve():
    N, K = map(int, input().split())
    A = list(map(int, input().split()))

    MOD = 10**9 + 7

    num_zero = 0
    neg_list = []
    pos_list = []
    for a in A:
        if a == 0:
            num_zero += 1
        elif a < 0:
            neg_list.append(a)
        else:
            pos_list.append(a)

    # 0にしかできない
    if len(pos_list) + len(neg_list) < K:
        print(0)
    else:
        min_num_neg = K - len(pos_list)
        max_num_neg = min(K, len(neg_list))
        # 負にしかできない
        if min_num_neg == max_num_neg and min_num_neg % 2 == 1:
            if num_zero > 0:
                print(0)
                return

            ans = 1
            neg_list.sort()
            pos_list.sort(reverse=True)
            for i in range(K):
                use_pos = False
                if len(neg_list) == 0 or len(pos_list) == 0:
                    if len(neg_list) == 0:
                        use_pos = True
                    else:
                        use_pos = False
                elif abs(neg_list[-1]) < pos_list[-1]:
                    use_pos = False
                else:
                    use_pos = True

                if use_pos:
                    ans *= pos_list[-1]
                    pos_list.pop()
                else:
                    ans *= neg_list[-1]
                    neg_list.pop()

                ans %= MOD

            print(ans)

        else:
            # 正にできる
            ans = 1

            neg_list.sort(reverse=True)
            pos_list.sort()

            if K % 2 == 1:
                K -= 1
                ans *= pos_list[-1]
                pos_list.pop()

            # posもnegも偶数個ずつ使う
            for _ in range(0, K, 2):
                use_pos = False
                if len(neg_list) <= 1 or len(pos_list) <= 1:
                    if len(neg_list) <= 1:
                        use_pos = True
                    else:
                        use_pos = False
                elif abs(neg_list[-1] * neg_list[-2]) > (pos_list[-1] * pos_list[-2]):
                    use_pos = False
                else:
                    use_pos = True

                if use_pos:
                    ans *= pos_list[-1] * pos_list[-2]
                    pos_list.pop()
                    pos_list.pop()
                else:
                    ans *= neg_list[-1] * neg_list[-2]
                    neg_list.pop()
                    neg_list.pop()

                ans %= MOD

            print(ans)


def main():
    solve()


if __name__ == '__main__':
    main()
