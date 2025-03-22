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

// clang-format off
#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for (int i = (a); i < (n); ++i)
#define FOE(i, a) for (auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define BIT_COUNT32(bit) (__builtin_popcount(bit))
#define BIT_COUNT64(bit) (__builtin_popcountll(bit))

template<typename T> using MinPriorityQueue = std::priority_queue<T, std::vector<T>, std::greater<T>>;
template<typename T> using MaxPriorityQueue = std::priority_queue<T>;

typedef long long LL;
typedef __int128_t LLL;
template<typename T> std::vector<T> make_v(size_t a){return std::vector<T>(a);}
template<typename T,typename... Ts> auto make_v(size_t a, Ts... ts){ return std::vector<decltype(make_v<T>(ts...))>(a,make_v<T>(ts...));}    // C++14
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value==0>::type fill_v(T &t,const V &v){t=v;}
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value!=0>::type fill_v(T &t,const V &v){for(auto &e:t) fill_v(e,v);}
template<class T> inline T ceil(T a, T b) { return (a + b - 1) / b; }
void print() { std::cout << "\n"; }
template <class Head, class... Tail> void print(Head&& head, Tail&&... tail) { std::cout << head; if (sizeof...(tail) != 0) {std::cout << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void print(std::vector<T> &v) {for (auto& a : v) { std::cout << a; if (&a != &v.back()) {std::cout << " ";} }std::cout << "\n";}
template <class T> void print(std::pair<T, T> &p) { std::cout << p.first << " " << p.second << "\n"; }
void debug() { std::cerr << "\n"; }
template <class Head, class... Tail> void debug(Head&& head, Tail&&... tail) { std::cerr << head; if (sizeof...(tail) != 0) {std::cerr << " ";} debug(std::forward<Tail>(tail)...); }
template <class T> void debug(std::vector<T> &v) {for (auto& a : v) { std::cerr << a; if (&a != &v.back()) {std::cerr << " ";} }std::cerr << "\n";}
template <class T> void debug(std::pair<T, T> &p) { std::cerr << p.first << " " << p.second << "\n"; }
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
// clang-format on

using namespace std;

// #include <numeric>
// #include <set>
// #include <vector>

class UnionFind {
public:
    const int num_nodes; // 要素の個数
    int set_size; // 集合の個数
    std::set<int> leaders;

private:
    std::vector<int> parent; // 親の番号(親だった場合は-(その集合のサイズ))
    std::vector<int> next;

public:
    explicit UnionFind(const int num_nodes) : num_nodes(num_nodes), set_size(num_nodes), parent(num_nodes, -1) {
        this->next.resize(num_nodes);
        std::iota(this->next.begin(), this->next.end(), 0);
        for (int u = 0; u < num_nodes; ++u) {
            this->leaders.insert(u);
        }
    }

    // u と v が同じ集合に属するか判定する
    bool is_same_set(const int u, const int v) {
        return this->find_root(u) == this->find_root(v);
    }

    // u と v の属する集合を併合する
    bool unite(int u, int v) {
        u = this->find_root(u);
        v = this->find_root(v);
        if (u == v) {
            return false;
        }

        // 集合のサイズが大きい方を u とする
        if (this->parent[u] > this->parent[v]) {
            std::swap(u, v);
        }

        // u の下に v をつける
        this->parent[u] += this->parent[v];
        this->parent[v] = u;
        std::swap(this->next[v], this->next[u]);
        this->set_size--;
        this->leaders.erase(v);

        return true;
    }

    // u の属する集合の要素数を求める
    int size(const int u) {
        return (-this->parent[this->find_root(u)]);
    }

    int leader(const int u) {
        return this->find_root(u);
    }

    // u の所属する集合のメンバーを求める
    // O(メンバーの人数)
    std::vector<int> group(const int u) {
        std::vector<int> group(this->size(u));
        int now = this->find_root(u);
        for (int i = 0; i < (int) group.size(); ++i) {
            group[i] = now = this->next[now];
        }
        return group;
    }

private:
    // 木の根を求める
    int find_root(const int u) {
        if (this->parent[u] < 0) {
            return u;
        } else {
            return this->parent[u] = this->find_root(this->parent[u]);
        }
    }
};

template<typename T>
class Edge {
public:
    int from;
    int to;
    T w;
    int no;

    Edge() : from(-1), to(-1), w(-1), no(-1) {}

    Edge(int from, int to, T w = 1, int no = -1) : from(from), to(to), w(w), no(no) {}
};

template<typename T = int>
class Tree {
private:
    bool build_done = false;

public:
    const int num_nodes;
    std::vector<std::vector<Edge<T>>> graph;
    std::vector<int> parent;
    std::vector<std::vector<Edge<T>>> children;
    std::vector<int> depth;
    std::vector<int> num_children;

    explicit Tree(const int num_nodes) : num_nodes(num_nodes), graph(num_nodes) {}

    void add_directed_edge(const int u, const int v, const T w = 1, const int no = -1) {
        this->graph[u].emplace_back(Edge(u, v, w, no));
    }

    void add_undirected_edge(const int u, const int v, const T w = 1, const int no = -1) {
        this->graph[u].emplace_back(Edge(u, v, w, no));
        this->graph[v].emplace_back(Edge(v, u, w, no));
    }

    std::vector<Edge<T>> &operator[](const int u) {
        return this->graph[u];
    }

    void build(const int root) {
        if (not this->build_done) {
            this->parent.resize(this->num_nodes, -1);
            this->children.resize(this->num_nodes);
            this->depth.resize(this->num_nodes);
            this->num_children.resize(this->num_nodes);
            this->dfs(root, -1, 0);
        }
        this->build_done = true;
    }

private:
    // 各ノード u について，親，子供，深さ，u を根とする部分木のサイズを求める
    int dfs(const int u, const int p, const int d) {
        this->parent[u] = p;
        this->depth[u] = d;
        this->num_children[u] = 1;
        for (const auto &e: this->graph[u]) {
            if (e.to != p) {
                this->children[u].emplace_back(e);
                this->num_children[u] += this->dfs(e.to, u, d + 1);
            }
        }
        return this->num_children[u];
    }
};

// #include <algorithm>
// #include <cmath>
// #include <stack>
// #include <unordered_map>
// #include <vector>
// #include "library/tree/Tree.hpp"

// 木の距離に関する関数まとめ
template<typename T>
class TreeUtility {
private:
    int log_v = 0;
    std::vector<std::vector<int>> parent; // 2^k 個上の親
    std::vector<T> distance_from_root; // 根からの距離

public:
    Tree<T> tree;
    std::vector<int> depth; // 根からの深さ

    explicit TreeUtility(Tree<T> &tree) : tree(tree) {
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
                    this->parent[k + 1][u] =
                            this->parent[k]
                                        [this->parent[k]
                                                     [u]]; // uの2^k個上のノードの2^k上のノードはuの2^(k+1)個上のノード
                }
            }
        }
    }

    // u と v の距離を求める
    // O(log N)
    [[nodiscard]] T distance(const int u, const int v) const {
        return this->distance_from_root[u] + this->distance_from_root[v] -
               2 * this->distance_from_root[this->lca(u, v)];
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
        const auto [u, _] = this->max_distance(0); // 頂点 0 から一番遠い頂点を探す
        const auto [v, diameter] = this->max_distance(u); // 頂点 u から一番遠い頂点を探す
        return {u, v, diameter};
    }

    // 木の中心(重みを考慮していないことに注意)
    // 木の直径が奇数の場合，辺になるので頂点を2つ返す
    std::pair<int, int> center() const {
        const auto [u, v, d] = this->diameter();
        const auto path = this->construct_path(u, v);

        if (d % 2 == 0) {
            return {path[d / 2].from, path[d / 2].from};
        } else {
            return {path[d / 2].from, path[d / 2].to};
        }
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

    // from から to へのパスを求める
    // O(N + M)
    std::vector<Edge<T>> construct_path(const int from, const int to) const {
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

            for (const auto &e: this->tree.graph[u]) {
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
    vector<int> P(N);
    FOR(i, 0, N) {
        cin >> P[i];
        P[i]--;
    }

    UnionFind uf(N);
    vector<int> deg(N);
    Tree tree(N);
    int M;
    cin >> M;
    FOR(i, 0, M) {
        int A, B;
        cin >> A >> B;
        A--;
        B--;
        if (uf.unite(A, B)) {
            tree.add_undirected_edge(A, B, 0, i + 1);
            deg[A]++;
            deg[B]++;
        }
    }

    queue<int> que;
    FOR(u, 0, N) {
        if (deg[u] == 1) {
            que.emplace(u);
        }
    }

    vector<int> ans;
    TreeUtility tu(tree);
    tu.build(0);
    while (not que.empty()) {
        const int u = que.front();
        que.pop();

        int v = -1;
        FOR(a, 0, N) {
            if (P[a] == u) {
                v = a;
                break;
            }
        }
        assert(P[v] == u);
        if (not uf.is_same_set(u, v)) {
            break;
        }

        // v の値 を u にもっていく
        const auto path = tu.construct_path(v, u);
        FOE(e, path) {
            ans.emplace_back(e.no);
            swap(P[e.from], P[e.to]);
        }
        assert(P[u] == u);

        deg[u]--;
        FOE(e, tree[u]) {
            deg[e.to]--;
            if (deg[e.to] == 1) {
                que.emplace(e.to);
            }
        }
    }

    FOR(i, 0, N) {
        if (P[i] != i) {
            print(-1);
            return 0;
        }
    }
    print(LEN(ans));
    print(ans);

    return 0;
}
