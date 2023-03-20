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

class Point {
public:
    int no;
    int x;
    int y;

    Point() : no(0), x(0), y(0) {}
    Point(int no, int x, int y) : no(no), x(x), y(y) {}

    bool operator<(const Point &another) const {
        if (x != another.x) {
            return x < another.x;
        }
        if (y != another.y) {
            return y < another.no;
        }
        return no < another.no;
    };
};

// 各点について，左上，左下，右上，右下に存在する点の数を求める
// 自身は含まない．また，自分と同じ線上のものは含まない）
// 点の位置の値が大きいなら座標圧縮すること
// O(N log N) くらい
std::vector<std::tuple<int, int, int, int>> line_sweep(std::vector<Point> &points) {
    const int N = (int)points.size();
    const int maxi = N + 100;	// 点の最大の値
    vector<tuple<int, int, int, int>> ans(N);

    std::sort(points.begin(), points.end()); // xでソート

    // 左上と左下の点の個数を求める
    {
        FenwickTree<int> ft(maxi);
        for (int i = 0; i < N; ++i) {
            const auto point = points[i];
            assert(point.y < maxi);
            const auto num = ft.sum(point.y);
            std::get<0>(ans[point.no]) = i - num; // 左上
            std::get<1>(ans[point.no]) = num;     // 左下
            ft.add(point.y, 1);
        }
    }

    // 右上と右下の点の個数を求める
    {
        FenwickTree<int> ft(maxi);
        for (int i = N - 1; i >= 0; --i) {
            const auto point = points[i];
            assert(point.y < maxi);
            const auto num = ft.sum(point.y);
            std::get<2>(ans[point.no]) = (N - i - 1) - num;   // 右上
            std::get<3>(ans[point.no]) = num;                 // 右下
            ft.add(point.y, 1);
        }
    }

    return ans;
}

#include <vector>
#include <set>
#include <unordered_map>


template <class T=long long> class CoordinateCompression {
public:
    int no = 0;
    std::unordered_map<T, int> zip;    // 元の値 -> 圧縮した値
    std::unordered_map<int, T> unzip;  // 圧縮した値 -> 元の値

    CoordinateCompression() {
    }

    CoordinateCompression(const std::vector<T> &v) {
        this->build(v);
    }

    CoordinateCompression(const std::set<T> &v) {
        this->build(v);
    }

    void build(const std::vector<T> &v) {
        std::set<T> s(v.begin(), v.end());
        this->build(s);
    }

    void build(const std::set<T> &s) {
        for (auto x : s) {
            this->zip[x] = this->no;
            this->unzip[this->no] = x;
            this->no++;
        }
    }

    // デバッグ用(恒等写像)
    void debug_build(const std::vector<T> &v) {
        std::set<T> s(v.begin(), v.end());
        this->debug_build(s);
    }
    void debug_build(const std::set<T> &s) {
        for (auto x : s) {
            this->zip[x] = x;
            this->unzip[x] = x;
        }
    }
};


template<int mod> struct mint {
    long long x;
    mint(long long x = 0) : x(x % mod) {
    }

    mint& operator+=(const mint a) {
        if ((x += a.x) >= mod) {
            x -= mod;
        }
        return *this;
    }
    mint& operator-=(const mint a) {
        if ((x += mod-a.x) >= mod) {
            x -= mod;
        }
        return *this;
    }
    mint& operator*=(const mint a) {
        (x *= a.x) %= mod;
        return *this;
    }
    mint operator+(const mint a) const {
        mint res(*this);
        return res+=a;
    }
    mint operator-(const mint a) const {
        mint res(*this);
        return res-=a;
    }
    mint operator*(const mint a) const {
        mint res(*this);
        return res*=a;
    }
    mint pow(long long t) const {
        if (!t) {
            return 1;
        }
        mint a = pow(t>>1);
        a *= a;
        if (t&1) {
            a *= *this;
        }
        return a;
    }

    // mod が素数のときのみ利用可能
    mint inv() const {
        return pow(mod-2);
    }
    mint& operator/=(const mint a) {
        return (*this) *= a.inv();
    }
    mint operator/(const mint a) const {
        mint res(*this);
        return res/=a;
    }
};

const int MOD = 998244353;

// 左上，左下，右上，右下
mint<MOD> calc(int lu, int ld, int ru, int rd, int N) {
    mint<MOD> ans = 0;

    // 自分以外の点を選ぶ
    vector<int> num = {lu, ld, ru, rd};
    vector<int> bit = {0b1001, 0b0101, 0b1010, 0b0110};
    FOR(b, 0, 1 << 4) {
        mint<MOD> count = 1;
        int use_bit = 0;
        FOR(i, 0, 4) {
            if (is_bit_on(b, i)) {
                count *= (mint<MOD>(2).pow(num[i]) - 1);
                use_bit |= bit[i];
            }
        }
        // 上下左右全部選べた
        if (use_bit == 0b1111) {
            ans += count;
        }
    }

    // 自分を選ぶ
    ans += mint<MOD>(2).pow(N - 1);
    return ans;
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;
    vector<Point> points(N);
    set<int> ys, xs;
    FOR(i, 0, N) {
        int X, Y;
        cin >> X >> Y;
        points[i] = Point(i, X, Y);
        xs.insert(X);
        ys.insert(Y);
    }

    CoordinateCompression cc_x(xs), cc_y(ys);
    FOR(i, 0, N) {
        points[i].x = cc_x.zip[points[i].x];
        points[i].y = cc_y.zip[points[i].y];
    }

    mint<MOD> ans;
    auto res = line_sweep(points);
    // 左上，左下，右上，右下
    for (auto [a, b, c, d] : res) {
        ans += calc(a, b, c, d, N);
    }

    print(ans.x);

    return 0;
}