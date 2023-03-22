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


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int K, X, Y;
    cin >> K;
    cin >> X >> Y;

    // X >= Y >= 0にする
    bool flag_x = false, flag_y = false, flag_swap = false;
    if (X < 0) {
        X *= -1;
        flag_x = true;
    }
    if (Y < 0) {
        Y *= -1;
        flag_y = true;
    }
    if (X < Y) {
        std::swap(X, Y);
        flag_swap = true;
    }

    // K が偶数なら偶奇が一致しないとだめ
    if (K % 2 == 0 and (X + Y) % 2 == 1) {
        print(-1);
        return 0;
    }

    auto minimum_step = max(ceil(X + Y, K), 2);
    // 偶奇が一致しないときは1回増やす
    if ((X + Y) % 2 != (minimum_step * K) % 2) {
        minimum_step++;
    }

    auto ans = make_v<pair<LL, LL>>(0);
    if (X + Y == K) {
        // ストレートにいける
        ans.push_back({X, Y});
    }
    else if (minimum_step == 3 && X < K) {
        LL mid = (K + X - Y) / 2;
        ans.push_back({X, X - K});
        ans.push_back({X + mid, Y - K + mid});
        ans.push_back({X, Y});
    }
    else {
        LL over = (minimum_step * K - (X + Y)) / 2;
        for (LL i = 1; i <= minimum_step; ++i) {
            LL d = i * K;
            if (d <= Y + over) {
                // 上にいく
                ans.push_back({0, d});
            }
            else if (d <= Y + over + X) {
                // 上にちょっといってから右にいく
                ans.push_back({d - Y - over, Y + over});
            }
            else {
                // 下にいく
                ans.push_back({X, Y + (minimum_step - i) * K});
            }
        }
    }

    if (flag_swap) {
        FOR(i, 0, LEN(ans)) {
            swap(ans[i].first, ans[i].second);
        }
    }
    if (flag_x) {
        FOR(i, 0, LEN(ans)) {
            ans[i].first *= -1;
        }
    }
    if (flag_y) {
        FOR(i, 0, LEN(ans)) {
            ans[i].second *= -1;
        }
    }

    print(LEN(ans));
    FOR(i, 0, LEN(ans)) {
        print(ans[i].first, ans[i].second);
    }

    return 0;
}