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

#include <vector>

template<typename T> class Edge {
public:
    const int u;
    const int v;
    const T w;
    const int no;
    Edge(int u, int v, T w=1, int no=-1) : u(u), v(v), w(w), no(no) {

    }
};

template<typename T=int> class Graph {
public:
    const int num_nodes;
    int num_edges;
    std::vector<std::vector<Edge<T>>> graph;

    Graph(const int num_nodes) : num_nodes(num_nodes), num_edges(0) {
        this->graph.resize(num_nodes);
    }

    void add_directed_edge(const int u, const int v, const T w=1, const int no=-1) {
        this->graph[u].emplace_back(Edge(u, v, w, no));
        this->num_edges++;
    }

    void add_undirected_edge(const int u, const int v, const T w=1, const int no=-1) {
        this->graph[u].emplace_back(Edge(u, v, w, no));
        this->graph[v].emplace_back(Edge(v, u, w, no));
        this->num_edges += 2;
    }

    std::vector<Edge<T>> &operator[](const int u) {
        return this->graph[u];
    }
};

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

pair<LL, LL> dfs(int u, vector<bool> &used, Graph<int> &g) {
    LL num_x = 0, num_y = 0;
    if (u < g.num_nodes / 2) {
        num_x++;
    }
    else {
        num_y++;
    }
    used[u] = true;

    FOE(e, g[u]) {
        if (not used[e.v]) {
            auto [x, y] = dfs(e.v, used, g);
            num_x += x;
            num_y += y;
        }
    }

    return {num_x, num_y};
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;

    auto points = make_v<pair<int, int>>(N);
    set<int> xs, ys;
    FOR(i, 0, N) {
        int X, Y;
        cin >> X >> Y;
        points[i] = {X, Y};
        xs.insert(X);
        ys.insert(Y);
    }

    CoordinateCompression<int> cc_x(xs), cc_y(ys);

    Graph<int> g(2 * N);
    for (auto [x, y] : points) {
        x = cc_x.zip[x];
        y = N + cc_y.zip[y];
        g.add_undirected_edge(x, y);
    }

    long long ans = 0;
    auto used = make_v<bool>(2 * N);
    FOR(u, 0, 2 * N) {
        if (not used[u]) {
            auto [num_x, num_y] = dfs(u, used, g);
            ans += num_x * num_y;
        }
    }
    ans -= N;
    print(ans);

    return 0;
}