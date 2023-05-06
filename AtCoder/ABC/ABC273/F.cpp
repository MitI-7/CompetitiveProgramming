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
#include <memory>

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

// sqrt(x)の整数解を求める
// 整数回がなければ-1
long long sqrt_integer(const long long x) {
    if (x < 0) {
        return -1;
    }
    auto a = (long long)sqrt(x);
    if (a * a == x) {
        return a;
    }
    if((a - 1) * (a - 1) == x) {
        return a - 1;
    }
    if((a + 1) * (a + 1) == x) {
        return a + 1;
    }

    return -1;
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

template<class T=long long>
class CoordinateCompression {
private:
    bool initialized;
    std::set<T> s;

    int no = 0;
    std::unordered_map<T, int> _zip;    // 元の値 -> 圧縮した値
    std::unordered_map<int, T> _unzip;  // 圧縮した値 -> 元の値
public:
    CoordinateCompression() : initialized(false) {}

    void add(T x) {
        this->s.insert(x);
    }

    int size() {
        if (not initialized) {
            this->build();
        }
        return no;
    }

    int zip(T x) {
        if (not initialized) {
            this->build();
        }
        return this->_zip[x];
    }

    T unzip(int i) {
        if (not initialized) {
            this->build();
        }
        return this->_unzip[i];
    }

private:
    void build() {
        this->initialized = true;
        for (auto x: this->s) {
            this->_zip[x] = this->no;
            this->_unzip[this->no] = x;
            this->no++;
        }
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, X;
    cin >> N >> X;
    vector<int> Y(N), Z(N);
    map<int, int> key_pos;
    CoordinateCompression<int> cc;
    cc.add(0);
    cc.add(X);

    FOR(i, 0, N) {
        cin >> Y[i];
        cc.add(Y[i]);
    }
    FOR(i, 0, N) {
        cin >> Z[i];
        cc.add(Z[i]);
    }

    FOR(i, 0, N) {
        Y[i] = cc.zip(Y[i]);
        Z[i] = cc.zip(Z[i]);
    }

    // dp[i][j][b] = 区間[i, j]は探索済みで，今 i or j にいるときの最短距離
    auto dp = make_v<LL>(cc.size() + 10, cc.size() + 10, 2);
    fill_v(dp, LINF);
    dp[cc.zip(0)][cc.zip(0)][0] = 0;
    dp[cc.zip(0)][cc.zip(0)][1] = 0;

    // 壁のインデックスとその番号の対応
    vector<int> wall(cc.size(), -1);
    FOR(i, 0, N) {
        wall[Y[i]] = i;
    }

    auto dist = [&](int l, int r) {
        return abs(cc.unzip(l) - cc.unzip(r));
    };

    LL ans = LINF;
    for (int l = cc.zip(0); l >= 0; --l) {
        FOR(r, cc.zip(0), cc.size()) {

            chmin(dp[l][r][1], dp[l][r][0] + dist(l, r));   // l -> rにいく
            chmin(dp[l][r][0], dp[l][r][1] + dist(l, r));   // r -> lにいく

            // lを左に伸ばす
            if (l - 1 >= 0) {
                int wall_no = wall[l - 1];
                // l - 1 がハンマーか，ハンマーを取得済みの壁なら通れる
                if (wall_no == -1 or (l <= Z[wall_no] and Z[wall_no] <= r)) {
                    chmin(dp[l - 1][r][0], dp[l][r][0] + dist(l - 1, l));
                }
            }

            // rを右に伸ばす
            if (r + 1 < cc.size()) {
                int wall_no = wall[r + 1];
                if (wall_no == -1 or (l <= Z[wall_no] and Z[wall_no] <= r)) {
                    chmin(dp[l][r + 1][1], dp[l][r][1] + dist(r, r + 1));
                }
            }

            if (l <= cc.zip(X) and cc.zip(X) <= r) {
                chmin(ans, dp[l][r][0]);
                chmin(ans, dp[l][r][1]);
            }
        }
    }

    if (ans == LINF) {
        print(-1);
    } else {
        print(ans);
    }

    return 0;
}