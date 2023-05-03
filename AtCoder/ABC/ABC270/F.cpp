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

#include <vector>

class UnionFind {
public:
    const int n;        // 要素の個数
    int set_size;       // 集合の個数

private:
    std::vector<int> parent;    // 親の番号(親だった場合は-(その集合のサイズ))

public:
    UnionFind(int n) : n(n), set_size(n), parent(n, -1) {
    }

    // x と y が同じ集合に属するか判定する
    bool is_same_set(const int x, const int y) {
        return this->find_root(x) == this->find_root(y);
    }

    // x と y の属する集合を併合する
    void union_set(int x, int y) {
        x = this->find_root(x);
        y = this->find_root(y);
        if (x == y) {
            return;
        }
        if (this->parent[x] > this->parent[y]) {
            std::swap(x, y);
        }

        // 小さい方(x)に大きい方(y)をくっつける
        // 両方ともrootなので-(集合のサイズ)が入っている
        this->parent[x] += this->parent[y];
        // yの親をxにする
        this->parent[y] = x;
        set_size--;
    }

    // xの属する集合の要素数を求める
    int size(const int x) {
        return (-this->parent[find_root(x)]);
    }

private:
    // 木の根を求める
    int find_root(const int x) {
        if (this->parent[x] < 0) {
            return x;
        } else {
            return this->parent[x] = find_root(this->parent[x]);
        }
    }
};


struct Edge {
    int no;
    int from;
    int to;
    long long cost;

    Edge() {}

    Edge(int from, int to, long long cost) : from(from), to(to), cost(cost) {}

    Edge(int no, int from, int to, long long cost) : no(no), from(from), to(to), cost(cost) {}

    bool operator<(const Edge &edge) const {
        return this->cost < edge.cost;
    }

    bool operator>(const Edge &edge) const {
        return this->cost > edge.cost;
    }
};

// グラフの最小全域木を求める。O(|E| log|V|)
long long kruskal(int num_of_node, std::vector<Edge> &edges) {
    sort(edges.begin(), edges.end());

    UnionFind uf(num_of_node);
    long long ans = 0;
    for (const auto e: edges) {
        if (!uf.is_same_set(e.from, e.to)) {
            uf.union_set(e.from, e.to);
            ans += e.cost;
        }
    }

    if (uf.size(0) != num_of_node) {
        return LINF;
    }

    return ans;
}


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, M;
    cin >> N >> M;

    auto X = make_v<LL>(N);
    auto Y = make_v<LL>(N);
    FOR(i, 0, N) {
        cin >> X[i];
    }
    FOR(i, 0, N) {
        cin >> Y[i];
    }

    // 道，道+空，道+海，道+空+海
    vector<Edge> edges1, edges2, edges3, edges4;
    FOR(i, 0, M) {
        int A, B;
        LL Z;
        cin >> A >> B >> Z;
        A--;
        B--;
        edges1.emplace_back(Edge(0, A, B, Z));
        edges2.emplace_back(Edge(0, A, B, Z));
        edges3.emplace_back(Edge(0, A, B, Z));
        edges4.emplace_back(Edge(0, A, B, Z));
    }

    const int a = N;
    const int f = a + 1;
    FOR(i, 0, N) {
        edges2.emplace_back(Edge(1, i, a, X[i]));

        edges3.emplace_back(Edge(2, i, a, Y[i]));

        edges4.emplace_back(Edge(1, i, a, X[i]));
        edges4.emplace_back(Edge(2, i, f, Y[i]));
    }

    LL ans = LINF;
    chmin(ans, kruskal(N, edges1));
    chmin(ans, kruskal(N + 1, edges2));
    chmin(ans, kruskal(N + 1, edges3));
    chmin(ans, kruskal(N + 2, edges4));
    print(ans);


    return 0;
}
