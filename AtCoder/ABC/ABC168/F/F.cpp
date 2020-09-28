#include <iostream>
#include <array>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <math.h>
#include <string>
#include <climits>
#include <assert.h>
#include <iomanip>
#include <bitset>
#include <queue>
#include <deque>
#include <stack>
#include <functional>
#include <fstream>
#include <random>

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for(int i=(a);i<(n); ++i)
#define FOE(i, a) for(auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define SUM(x) std::accumulate(ALL(x), 0LL)
#define MIN(v) *std::min_element(v.begin(), v.end())
#define MAX(v) *std::max_element(v.begin(), v.end())
#define EXIST(v, x) (std::find(v.begin(), v.end(), x) != v.end())
#define BIT_COUNT(bit) (__builtin_popcount(bit))

typedef long long LL;

template<typename T>
std::vector<T> make_v(size_t a) { return std::vector<T>(a); }

template<typename T, typename... Ts>
auto make_v(size_t a, Ts... ts) { return std::vector<decltype(make_v<T>(ts...))>(a, make_v<T>(ts...)); }    // C++14
template<typename T, typename V>
typename std::enable_if<std::is_class<T>::value == 0>::type fill_v(T &t, const V &v) { t = v; }

template<typename T, typename V>
typename std::enable_if<std::is_class<T>::value != 0>::type fill_v(T &t, const V &v) { for (auto &e:t) fill_v(e, v); }

template<class T>
inline T ceil(T a, T b) { return (a + b - 1) / b; }

void print() { std::cout << std::endl; }

template<class Head, class... Tail>
void print(Head &&head, Tail &&... tail) {
    std::cout << head;
    if (sizeof...(tail) != 0) { std::cout << " "; }
    print(std::forward<Tail>(tail)...);
}

template<class T>
void print(std::vector<T> &v) {
    for (auto &a : v) {
        std::cout << a;
        if (&a != &v.back()) { std::cout << " "; }
    }
    std::cout << std::endl;
}

template<class T>
void print(std::vector<std::vector<T>> &vv) { for (auto &v : vv) { print(v); }}

void debug() { std::cerr << std::endl; }

template<class Head, class... Tail>
void debug(Head &&head, Tail &&... tail) {
    std::cerr << head;
    if (sizeof...(tail) != 0) { std::cerr << " "; }
    print(std::forward<Tail>(tail)...);
}

template<class T>
void debug(std::vector<T> &v) {
    for (auto &a : v) {
        std::cerr << a;
        if (&a != &v.back()) { std::cerr << " "; }
    }
    std::cerr << std::endl;
}

template<class T>
void debug(std::vector<std::vector<T>> &vv) { for (auto &v : vv) { print(v); }}

inline bool inside(long long y, long long x, long long H, long long W) { return 0 <= y and y < H and 0 <= x and x < W; }

template<class T>
inline double euclidean_distance(T y1, T x1, T y2, T x2) { return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)); }

template<class T>
inline double manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }

template<typename T>
T &chmin(T &a, const T &b) { return a = std::min(a, b); }

template<typename T>
T &chmax(T &a, const T &b) { return a = std::max(a, b); }

bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }

unsigned long long bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) {
    assert(b == 0 or b == 1);
    if (b == 0) { return bit & ~(1ull << i); }
    else { return bit | (1ull << i); }
}

template<class T>
inline std::vector<T> unique(std::vector<T> v) {
    sort(v.begin(), v.end());
    v.erase(unique(v.begin(), v.end()), v.end());
    return v;
}

long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}


bool is_power_of_two(long long x) {
    return !(x & (x - 1));
}


long long gcd(long long a, long long b) {
    if (b == 0) { return a; }
    return gcd(b, a % b);
}


long long gcd(std::vector<long long> &v) {
    long long ans = v[0];
    for (int i = 1; i < (int) v.size(); ++i) {
        ans = gcd(ans, v[i]);
    }
    return ans;
}


long long lcm(long long a, long long b) {
    long long g = gcd(a, b);
    return a / g * b;
}

const int INF = 1u << 30u;
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
const std::vector<int> dy2 = {0, 1}, dx2 = {1, 0};
const std::vector<int> dy4 = {0, 1, 0, -1}, dx4 = {1, 0, -1, 0};
const std::vector<int> dy8 = {0, -1, 0, 1, 1, -1, -1, 1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};

using namespace std;

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

void paint(int sy, int sx, vector<vector<int>> &f) {
    queue<pair<int, int>> que;
    que.emplace(make_pair(sy, sx));
    while (not que.empty()) {
        int y, x;
        tie(y, x) = que.front(); que.pop();
        FOR(i, 0, 4) {
            int ny = dy4[i] + y;
            int nx = dx4[i] + x;
            if (inside(ny, nx, LEN(f), LEN(f[0]))) {
                if (f[ny][nx] == 0) {
                    f[ny][nx] = 2;
                    que.emplace(make_pair(ny, nx));
                }
            }
        }
    }
}


int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);

    LL N, M;
    cin >> N >> M;

    set<LL> ys, xs;
    ys.insert(0);
    xs.insert(0);

    auto h = make_v<tuple<LL, LL, LL>>(N);
    auto v = make_v<tuple<LL, LL, LL>>(M);
    FOR(i, 0, N) {
        LL y1, y2, x;
        cin >> y1 >> y2 >> x;
        h[i] = make_tuple(y1, y2, x);
        ys.insert(y1);
        ys.insert(y2);
        xs.insert(x);
    }

    FOR(i, 0, M) {
        LL y, x1, x2;
        cin >> y >> x1 >> x2;
        v[i] = make_tuple(y, x1, x2);
        ys.insert(y);
        xs.insert(x1);
        xs.insert(x2);
    }

    CoordinateCompression<LL> cc_y, cc_x;
    cc_y.build(ys);
    cc_x.build(xs);

    auto f = make_v<int>(cc_y.no * 2, cc_x.no * 2);
    FOE(t, h) {
        LL y1, y2, x;
        tie(y1, y2, x) = t;
        y1 = cc_y.zip[y1] * 2;
        y2 = cc_y.zip[y2] * 2;
        x = cc_x.zip[x] * 2;

        assert(y1 < y2);
        FOR(y, y1, y2 + 1) {
            f[y][x] = 1;
        }
    }

    FOE(t, v) {
        LL y, x1, x2;
        tie(y, x1, x2) = t;
        y = cc_y.zip[y] * 2;
        x1 = cc_x.zip[x1] * 2;
        x2 = cc_x.zip[x2] * 2;

        assert(x1 < x2);
        FOR(x, x1, x2 + 1) {
            f[y][x] = 1;
        }
    }


    paint(cc_y.zip[0] * 2, cc_x.zip[0] * 2, f);

    // inf check
    FOR(y, 0, LEN(f)) {
        if (f[y][0] == 2 or f[y][LEN(f[0]) - 1] == 2) {
            print("INF");
            return 0;
        }
    }

    FOR(x, 0, LEN(f[0])) {
        if (f[0][x] == 2 or f[LEN(f) - 1][x] == 2) {
            print("INF");
            return 0;
        }
    }

    LL ans = 0;
    FOR(y, 0, LEN(f)) {
        FOR(x, 0, LEN(f[0])) {
            if (f[y][x] == 2) {
                if (y % 2 == 0 or x % 2 == 0) {
                    continue;
                }
                LL a = (cc_y.unzip[y / 2 + 1] - cc_y.unzip[y / 2]);
                LL b = (cc_x.unzip[x / 2 + 1] - cc_x.unzip[x / 2]);
                ans += a * b;
            }
        }
    }
    print(ans);

    return 0;
}
