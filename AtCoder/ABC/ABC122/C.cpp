#include <iostream>
#include <array>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <cmath>
#include <string>
#include <climits>
#include <cassert>
#include <iomanip>
#include <bitset>
#include <queue>
#include <deque>
#include <stack>
#include <functional>
#include <fstream>
#include <random>
#include <complex>

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for(int i=(a);i<(n); ++i)
#define FOE(i, a) for(auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define SUM(x) std::accumulate(ALL(x), 0LL)
#define MIN(v) *std::min_element(v.begin(), v.end())
#define MAX(v) *std::max_element(v.begin(), v.end())
#define EXIST(v, x) (std::find(v.begin(), v.end(), x) != v.end())
#define BIT_COUNT32(bit) (__builtin_popcount(bit))
#define BIT_COUNT64(bit) (__builtin_popcountll(bit))

// @formatter:off
typedef long long LL;
template<typename T> std::vector<T> make_v(size_t a){return std::vector<T>(a);}
template<typename T,typename... Ts> auto make_v(size_t a, Ts... ts){ return std::vector<decltype(make_v<T>(ts...))>(a,make_v<T>(ts...));}    // C++14
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value==0>::type fill_v(T &t,const V &v){t=v;}
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value!=0>::type fill_v(T &t,const V &v){for(auto &e:t) fill_v(e,v);}
template<class T> inline T ceil(T a, T b) { return (a + b - 1) / b; }
void print() { std::cout << std::endl; }
template <class Head, class... Tail> void print(Head&& head, Tail&&... tail) { std::cout << head; if (sizeof...(tail) != 0) {std::cout << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void print(std::vector<T> &v) {for (auto& a : v) { std::cout << a; if (&a != &v.back()) {std::cout << " ";} }std::cout << std::endl;}
template <class T> void print(std::vector<std::vector<T>> &vv) { for (auto& v : vv) { print(v); }}
void debug() { std::cerr << std::endl; }
template <class Head, class... Tail> void debug(Head&& head, Tail&&... tail) { std::cerr << head; if (sizeof...(tail) != 0) {std::cerr << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void debug(std::vector<T> &v) {for (auto& a : v) { std::cerr << a; if (&a != &v.back()) {std::cerr << " ";} }std::cerr << std::endl;}
template <class T> void debug(std::vector<std::vector<T>> &vv) { for (auto& v : vv) { print(v); }}
inline bool inside(long long y, long long x, long long H, long long W) {return 0 <= y and y < H and 0 <= x and x < W; }
template<class T> inline double euclidean_distance(T y1, T x1, T y2, T x2) { return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)); }
template<class T> inline T manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }
template<typename T> T &chmin(T &a, const T &b) { return a = std::min(a, b); }
template<typename T> T &chmax(T &a, const T &b) { return a = std::max(a, b); }
bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }
unsigned long long get_bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) { assert(b == 0 or b == 1); if (b == 0) { return bit & ~(1ull << i); } else {return bit | (1ull << i);}}

// 初項s交差d長さnの数列の和
long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}

// 三角数
long long triangular_number(long long n) {
    return n * (n + 1) / 2;
}

// xが2の階乗かどうか判定
bool is_power_of_two(long long x) {
    return !(x & (x - 1));
}

// O(log max(a, b))
long long gcd(long long a, long long b) {
    if (b == 0) { return a; }
    return gcd(b, a % b);
}

long long lcm(long long a, long long b) {
    long long g = gcd(a, b);
    return a / g * b;
}

const int INF = 1u << 30u;  // 1,073,741,824
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
// 2次元配列上での移動
const std::vector<int> dy2 = {0, 1}, dx2 = {1, 0};  // 右，下
const std::vector<int> dy4 = {0, 1, 0, -1}, dx4 = {1, 0, -1, 0};    // 右，下，左，上
const std::vector<int> dy6 = {0, -1, 0, 1, 1, 1}, dx6 = {1, 0, -1, 0, 1, -1};
const std::vector<int> dy8 = {0, -1, 0, 1, 1, -1, -1, 1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};
// @formatter:on

using namespace std;

#pragma once
#include <cassert>
#include <vector>

// すべて0-origin
template<class T=long long> class FenwickTree {
public:
    const int n;
    std::vector<T> v;

    // n: 要素数
    FenwickTree(const int n) : n(n) {
        this->v.assign(n + 1, 0);
    }

    // [NO TEST]
    // i 番目の要素を取得する
    // O(log n)
    T access(const int i) const {
        return this->sum(i, i + 1);
    }

    // 区間[0, i) の合計を求める
    // O(log n)
    T sum(int i) const {
        assert(0 <= i and i <= this->n);

        T s = 0;
        i -= 1;
        while (i >= 0) {
            s += this->v[i];
            i = (i & (i + 1)) - 1;
        }
        return s;
    }

    // 区間 [left, right) の合計を求める
    // O(log n)
    T sum(const int left, const int right) const {
        assert(left <= right);
        return this->sum(right) - this->sum(left);
    }

    // i 番目の要素に x を加える
    // O(log n)
    void add(int i, T x) {
        assert(i < this->n);

        while (i < this->n) {
            this->v.at(i) += x;
            i |= i + 1;
        }
    }

    // [NO TEST]
    // i 番目の要素を x にする
    // O(log n)
    void set(int i, T x) {
        assert(i < this->n);

        T now = this->access(i);
        this->add(i, x - now);
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, Q;
    string S;
    cin >> N >> Q;
    cin >> S;

    vector<int> ans;
    FenwickTree<int> ft(N);

    FOR(i, 0, LEN(S) - 1) {
        if (S[i] == 'A' and S[i + 1] == 'C') {
            ft.add(i, 1);
        }
    }

    FOR(_, 0, Q) {
        int L, R;
        cin >> L >> R;
        L--; R--;

        int r = ft.sum(R + 1);
        int l = ft.sum(L);

        if (R + 1 < N and S[R] == 'A' and S[R + 1] == 'C') {
            r--;
        }

        ans.emplace_back(r - l);
    }

    FOE(a, ans) {
        print(a);
    }

    return 0;
}