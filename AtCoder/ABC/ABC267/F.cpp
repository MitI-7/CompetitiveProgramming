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

template<typename T>
class Edge {
public:
    int from;
    int to;
    T w;
    int no;

    Edge() : from(-1), to(-1), w(-1), no(-1) {}

    Edge(int from, int to, T w = 1, int no = -1) : from(from), to(to), w(w), no(no) {

    }
};

template<typename T=int>
class Tree {
public:
    const int num_nodes;
    std::vector<std::vector<Edge<T>>> graph;

    explicit Tree(const int num_nodes) : num_nodes(num_nodes) {
        this->graph.resize(num_nodes);
    }

    // add undirected edge
    void add_edge(const int u, const int v, const T w = 1, const int no = -1) {
        this->graph[u].emplace_back(Edge(u, v, w, no));
        this->graph[v].emplace_back(Edge(v, u, w, no));
    }

    void add_child(const int p, int c, const T w = 1, const int no = -1) {
        this->graph[p].emplace_back(Edge(p, c, w, no));
    }

    std::vector<Edge<T>> &operator[](const int u) {
        return this->graph[u];
    }

    // from から to へのパスを求める
    // O(N + M)
    std::vector<Edge<T>> path(const int from, const int to) const {
        if (from == to) {
            return {};
        }

        // from -> to のパス
        std::unordered_map<int, Edge<T>> prev;
        std::stack<int> nodes;
        nodes.push(from);
        while (not nodes.empty()) {
            const auto u = nodes.top();
            nodes.pop();
            if (u == to) {
                break;
            }

            for (Edge<T> e: this->graph[u]) {
                if (prev.find(e.to) == prev.end()) {
                    prev[e.to] = e;
                    nodes.push(e.to);
                }
            }
        }

        std::vector<Edge<T>> path;
        int now = to;
        while (prev[now].from != from) {
            path.emplace_back(prev[now]);
            now = prev[now].from;
        }
        path.emplace_back(prev[now]);
        std::reverse(path.begin(), path.end());

        return path;
    }
};

// 木の距離に関する関数まとめ
template<typename T>
class TreeDistance {
private:
    int log_v = 0;
    std::vector<std::vector<int>> parent;       // 2^k 個上の親
    std::vector<T> distance_from_root;          // 根からの距離

public:
    Tree<T> tree;
    std::vector<int> depth;                     // 根からの深さ

    explicit TreeDistance(Tree<T> &tree) : tree(tree) {
        this->log_v = int(std::log2(tree.num_nodes)) + 1;
        this->parent.resize(this->log_v, std::vector<int>(tree.num_nodes));
        this->depth.resize(tree.num_nodes);
        this->distance_from_root.resize(tree.num_nodes);
    }

    // O(N log N)
    void build(const int root) {
        this->dfs(root, -1, 0);
        this->distance_from_root[root] = 0;
        if (tree.num_nodes == 0) {
            return;
        }

        // 各頂点の 2^k 個上の親を求める
        for (int k = 0; k + 1 < this->log_v; k++) {
            for (int u = 0; u < this->tree.num_nodes; ++u) {
                if (this->parent[k][u] < 0) {
                    this->parent[k + 1][u] = -1;
                } else {
                    this->parent[k + 1][u] = this->parent[k][this->parent[k][u]]; // uの2^k個上のノードの2^k上のノードはuの2^(k+1)個上のノード
                }
            }
        }
    }

    // u と v の距離を求める
    // O(log N)
    [[nodiscard]] T distance(const int u, const int v) const {
        return this->distance_from_root[u] + this->distance_from_root[v] - 2 * this->distance_from_root[this->lca(u, v)];
    }

    // u から一番遠い頂点とその距離を求める
    // 距離は辺の長さを考慮している点に注意
    // O(N log N)
    std::pair<int, T> max_distance(const int u) const {
        int v = 0;
        T max_distance = 0;
        for (int node = 0; node < this->tree.num_nodes; ++node) {
            auto dist = this->distance(u, node);
            if (dist > max_distance) {
                max_distance = dist;
                v = node;
            }
        }

        return {v, max_distance};
    }

    // 木の直径のうちのひとつのペアとその長さを求める
    // 距離は辺の長さを考慮している点に注意
    // O(N log N)
    std::tuple<int, int, T> diameter() const {
        const auto [u, _] = this->max_distance(0);       // 頂点 0 から一番遠い頂点を探す
        const auto [v, diameter] = this->max_distance(u);   // 頂点 u から一番遠い頂点を探す
        return {u, v, diameter};
    }

    // u と v の最近共通祖先の頂点
    // O(log N)
    [[nodiscard]] int lca(int u, int v) const {
        // v の方が深いようにする
        if (this->depth[u] > this->depth[v]) {
            std::swap(u, v);
        }
        // u と v の深さを揃える
        for (int k = 0; k < this->log_v; ++k) {
            if (((this->depth[v] - this->depth[u]) >> k) & 1u) {
                v = this->parent[k][v];
            }
        }

        if (u == v) {
            return u;
        }

        for (int k = this->log_v - 1; k >= 0; --k) {
            if (this->parent[k][u] != this->parent[k][v]) {
                u = this->parent[k][u];
                v = this->parent[k][v];
            }
        }

        return this->parent[0][u];
    }

    // u の 祖先のうち，深さ d である頂点を求める．存在しない場合は -1 を返す
    // u の d 個上に行きたいときは，depth[u] - d を渡せばいい
    // O(log N)
    [[nodiscard]] int level_ancestor(int u, int d) const {
        if (this->depth[u] < d) {
            return -1;
        }
        if (this->depth[u] == d) {
            return u;
        }

        int a = this->depth[u] - d; // a 個上に行く
        for (int k = this->log_v - 1; k >= 0; --k) {
            if (a >= (1 << k)) {
                u = this->parent[k][u];
                a -= (1 << k);
            }
        }
        return u;
    }

    // u から v のパスで k 番目の頂点を求める
    // なかったら -1 を返す
    [[nodiscard]] int jump(const int u, const int v, int k) const {
        int lca = this->lca(u, v);
        int u_depth = this->depth[u];
        int v_depth = this->depth[v];
        int lca_depth = this->depth[lca];

        int d1 = u_depth - lca_depth;
        int d2 = v_depth - lca_depth;

        if (k > d1 + d2) {
            return -1;
        }

        // u から lca までの間に k 番目の頂点がある
        if (d1 >= k) {
            return this->level_ancestor(u, u_depth - k);
        }
        k -= d1;

        // v から lca までの間に k 番目の頂点がある
        if (d2 >= k) {
            return this->level_ancestor(v, v_depth - (d2 - k));
        }

        return -1;
    }

private:
    // 以下を各頂点について求める
    // 1 つ上の親，深さ，根からの距離
    void dfs(const int u, const int p, const int d) {
        this->parent[0][u] = p;
        this->depth[u] = d;

        for (const auto e: this->tree.graph[u]) {
            if (e.to != p) {
                this->distance_from_root[e.to] = this->distance_from_root[u] + e.w;
                this->dfs(e.to, u, d + 1);
            }
        }
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;
    Tree<int> tree(N);
    FOR(i, 0, N - 1) {
        int A, B;
        cin >> A >> B;
        A--;
        B--;
        tree.add_edge(A, B);
    }

    TreeDistance<int> td(tree);
    td.build(0);
    auto [u1, u2, _] = td.diameter();

    int Q;
    cin >> Q;
    vector<int> ans(Q);
    FOR(i, 0, Q) {
        int U, K;
        cin >> U >> K;
        U--;

        int a = td.jump(U, u1, K);
        if (a == -1) {
            a = td.jump(U, u2, K);
        }
        ans[i] = a;
    }

    FOE(a, ans) {
        if (a != -1) {
            print(a + 1);
        } else {
            print(-1);
        }
    }

    return 0;
}