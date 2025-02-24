#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cmath>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for (int i = (a); i < (n); ++i)
#define FOE(i, a) for (auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define BIT_COUNT32(bit) (__builtin_popcount(bit))
#define BIT_COUNT64(bit) (__builtin_popcountll(bit))

template<typename T> using MinPriorityQueue = std::priority_queue<T, std::vector<T>, std::greater<T>>;
template<typename T> using MaxPriorityQueue = std::priority_queue<T>;

// @formatter:off
typedef long long LL;
typedef __int128_t LLL;
template<typename T> std::vector<T> make_v(size_t a){return std::vector<T>(a);}
template<typename T,typename... Ts> auto make_v(size_t a, Ts... ts){ return std::vector<decltype(make_v<T>(ts...))>(a,make_v<T>(ts...));}    // C++14
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value==0>::type fill_v(T &t,const V &v){t=v;}
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value!=0>::type fill_v(T &t,const V &v){for(auto &e:t) fill_v(e,v);}
template<class T> inline T ceil(T a, T b) { return (a + b - 1) / b; }
void print() { std::cout << std::endl; }
template <class Head, class... Tail> void print(Head&& head, Tail&&... tail) { std::cout << head; if (sizeof...(tail) != 0) {std::cout << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void print(std::vector<T> &v) {for (auto& a : v) { std::cout << a; if (&a != &v.back()) {std::cout << " ";} }std::cout << std::endl;}
template <class T> void print(std::pair<T, T> &p) { std::cout << p.first << " " << p.second << std::endl; }
void debug() { std::cerr << std::endl; }
template <class Head, class... Tail> void debug(Head&& head, Tail&&... tail) { std::cerr << head; if (sizeof...(tail) != 0) {std::cerr << " ";} debug(std::forward<Tail>(tail)...); }
template <class T> void debug(std::vector<T> &v) {for (auto& a : v) { std::cerr << a; if (&a != &v.back()) {std::cerr << " ";} }std::cerr << std::endl;}
template <class T> void debug(std::pair<T, T> &p) { std::cerr << p.first << " " << p.second << std::endl; }
inline bool inside(long long y, long long x, long long H, long long W) {return 0 <= y and y < H and 0 <= x and x < W; }
template<class T> inline double euclidean_distance(T y1, T x1, T y2, T x2) { return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)); }
template<class T> inline T euclidean_distance2(T y1, T x1, T y2, T x2) { return (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2); }
template<class T> inline T manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }
template<typename T> T &chmin(T &a, const T &b) { return a = std::min(a, b); }
template<typename T> T &chmax(T &a, const T &b) { return a = std::max(a, b); }
bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }
unsigned long long get_bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) { assert(b == 0 or b == 1); if (b == 0) { return bit & ~(1ull << i); } else {return bit | (1ull << i);}}

const int INF = 1u << 30u;  // 1,073,741,824
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
// 2次元配列上での移動．右，下，左，上，右上，右下，左下，左上
const std::vector<int> dy8 = {0, 1, 0, -1, -1, 1, 1, -1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};
// @formatter:on

using namespace std;

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);


     // 入力：グリッドの大きさ
    long long H, W;
    cin >> H >> W;

    // 2本の線の情報
    char t1, t2;
    long long v1, v2;
    cin >> t1 >> v1;
    cin >> t2 >> v2;

    // 結果となる交点 (y, x)
    long long x = 0, y = 0;
    bool valid = true;

    // 同じ種類同士は平行なので交点は存在しない
    if(t1 == t2) {
        valid = false;
    }
    // 縦線と横線の場合: (y, x) = (横の定数, 縦の定数)
    else if ((t1 == 'V' && t2 == 'H') || (t1 == 'H' && t2 == 'V')) {
        if(t1 == 'V'){
            x = v1;
            y = v2;
        } else {
            x = v2;
            y = v1;
        }
    }
    // 縦線と右ななめの場合: 縦線 x = c, 右ななめ x - y = d → y = c - d
    else if ((t1 == 'V' && t2 == 'R') || (t1 == 'R' && t2 == 'V')) {
        if(t1 == 'V'){
            x = v1;      // v1: c
            y = v1 - v2; // v2: d
        } else {
            x = v2;      // v2: c
            y = v2 - v1; // v1: d
        }
    }
    // 縦線と左ななめの場合: 縦線 x = c, 左ななめ x + y = d → y = d - c
    else if ((t1 == 'V' && t2 == 'L') || (t1 == 'L' && t2 == 'V')) {
        if(t1 == 'V'){
            x = v1;      // v1: c
            y = v2 - v1; // v2: d
        } else {
            x = v2;      // v2: c
            y = v1 - v2; // v1: d
        }
    }
    // 横線と右ななめの場合: 横線 y = c, 右ななめ x - y = d → x = d + c
    else if ((t1 == 'H' && t2 == 'R') || (t1 == 'R' && t2 == 'H')) {
        if(t1 == 'H'){
            y = v1;      // v1: y定数
            x = v2 + v1; // v2: d
        } else {
            y = v2;      // v2: y定数
            x = v1 + v2; // v1: d
        }
    }
    // 横線と左ななめの場合: 横線 y = c, 左ななめ x + y = d → x = d - c
    else if ((t1 == 'H' && t2 == 'L') || (t1 == 'L' && t2 == 'H')) {
        if(t1 == 'H'){
            y = v1;      // v1: y定数
            x = v2 - v1; // v2: d
        } else {
            y = v2;      // v2: y定数
            x = v1 - v2; // v1: d
        }
    }
    // 右ななめと左ななめの場合: 右ななめ x - y = d, 左ななめ x + y = d'
    else if ((t1 == 'R' && t2 == 'L') || (t1 == 'L' && t2 == 'R')) {
        // 右ななめの d と左ななめの d' を決定する
        long long dR, dL;
        if(t1 == 'R'){
            dR = v1;
            dL = v2;
        } else {
            dR = v2;
            dL = v1;
        }
        // 連立方程式より:
        //   x = (dR + dL) / 2,  y = (dL - dR) / 2
        if ((dR + dL) % 2 != 0 || (dL - dR) % 2 != 0) {
            valid = false;
        } else {
            x = (dR + dL) / 2;
            y = (dL - dR) / 2;
        }
    }
    else {
        valid = false;
    }

    // グリッド内かどうかのチェック
    if(valid) {
        if(x < 1 || x > W || y < 1 || y > H)
            valid = false;
    }

    if(valid)
        cout << y << " " << x << "\n";
    else
        cout << -1 << "\n";

    return 0;
}
