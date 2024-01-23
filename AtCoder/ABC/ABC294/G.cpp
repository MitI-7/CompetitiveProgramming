#include <bits/stdc++.h>

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for(int i=(a);i<(n); ++i)
#define FOE(i, a) for(auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
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
template <class T> void print(std::pair<T, T> &p) { std::cout << p.first << " " << p.second << std::endl; }
void debug() { std::cerr << std::endl; }
template <class Head, class... Tail> void debug(Head&& head, Tail&&... tail) { std::cerr << head; if (sizeof...(tail) != 0) {std::cerr << " ";} debug(std::forward<Tail>(tail)...); }
template <class T> void debug(std::vector<T> &v) {for (auto& a : v) { std::cerr << a; if (&a != &v.back()) {std::cerr << " ";} }std::cerr << std::endl;}
template <class T> void debug(std::pair<T, T> &p) { std::cerr << p.first << " " << p.second << std::endl; }
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
// 整数解がなければ-1
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
};

// 木の距離に関する関数まとめ
template<typename T>
class TreeDistance {
public:
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
                }
                else {
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

#include <vector>

template<typename T=int>
class EulerTour {
public:
    Tree<T> tree;
    std::vector<int> tour;   // ノードを dfs 順に並び替えた配列

private:
    std::vector<int> in;        // 各頂点について，最初に通った時刻
    std::vector<int> out;       // 各頂点について，最後に通った時刻
    std::vector<int> node_tour; // 各頂点の tour でのインデックス

public:
    explicit EulerTour(const Tree<T> &tree) : tree(tree) {
        this->in.resize(tree.num_nodes, -1);
        this->out.resize(tree.num_nodes, -1);
        this->node_tour.resize(tree.num_nodes, -1);
    }

    void build(const int root) {
        this->dfs(root, -1);
    }

    // ノード u の部分木の tour 上での区間 [l, r) を返す
    std::pair<int, int> range(const int u) const {
        return std::make_pair(this->in[u], this->out[u]);
    }

    // ノード u の tour でのインデックス
    int tour_idx(const int u) {
        return this->node_tour[u];
    }

private:
    int t = 0;

    void dfs(const int u, const int p) {
        this->in[u] = t++;
        this->tour.emplace_back(u);
        this->node_tour[u] = this->tour.size() - 1;
        for (auto edge: this->tree.graph[u]) {
            if (edge.to != p) {
                dfs(edge.to, u);
            }
        }
        this->out[u] = t;
    }
};

template<typename T>
struct Mode {
    std::function<T(T, T)> f;   // 要素に適用する演算
    std::function<T(T, T)> g;   // 作用素の適用
    std::function<T(T, T)> h;   // 作用素の合成
    std::function<T(T, int)> p;
    T unit;
    T lazy_unit;
};

template<typename T>
class LazySegmentTree {
private:
    const int array_size;
    int n;
    std::vector<T> data, lazy;
    const Mode<T> mode;
public:
    LazySegmentTree(const std::vector<T> &v, const Mode<T> mode) : array_size(v.size()), mode(mode) {
        this->n = 1;
        while (this->n < this->array_size) { this->n *= 2; }
        this->data.resize(2 * this->n - 1, this->mode.unit);
        this->lazy.resize(2 * this->n - 1, this->mode.lazy_unit);

        for (int i = 0; i < this->array_size; ++i) {
            this->data[i + n - 1] = v[i];
        }
        for (int i = this->n - 2; i >= 0; i--) {
            this->data[i] = this->mode.f(this->data[i * 2 + 1], this->data[i * 2 + 2]);
        }
    }

    // array[idx]
    // log(N)
    T access(const int idx) {
        return query(idx, idx + 1, 0, 0, this->n);
    }

    // operation(array[idx], x)
    // log(N)
    void operation(const int idx, const T x) {
        operation(idx, idx + 1, x);
    }

    // operation(array[left, right), x)
    // log(N)
    void operation(const int left, const int right, const T x) {
        assert(0 <= left and left < right and right <= this->array_size);
        operation(left, right, x, 0, 0, this->n);
    }

    // op(array[a, b))
    // log(N)
    T query(const int left, const int right) {
        return query(left, right, 0, 0, this->n);
    }

private:
    T operation(const int a, const int b, const T x, const int k, const int l, const int r) {
        propagate(k, r - l);

        // 範囲外
        if (b <= l or r <= a) {
            return this->data[k];
        }
            // 完全に含む
        else if (a <= l and r <= b) {
            this->lazy[k] = this->mode.h(this->lazy[k], x);
            propagate(k, r - l);
            return this->mode.g(this->data[k], this->mode.p(this->lazy[k], r - l));
        }
            // 一部含む
        else {
            auto lv = operation(a, b, x, 2 * k + 1, l, (l + r) / 2);    // 左の子
            auto rv = operation(a, b, x, 2 * k + 2, (l + r) / 2, r);    // 右の子
            return this->data[k] = this->mode.f(lv, rv);
        }
    }

    // [a, b)の目的値をノードk（区間[l, r]）から検索
    T query(const int a, const int b, const int k, const int l, const int r) {
        propagate(k, r - l);

        // 範囲外
        if (b <= l or r <= a) {
            return this->mode.unit;
        }
            // 完全に含む
        else if (a <= l && r <= b) {
            return this->data[k];
        }
            // 一部含む
        else {
            auto vl = query(a, b, k * 2 + 1, l, (l + r) / 2);    // 左の子
            auto vr = query(a, b, k * 2 + 2, (l + r) / 2, r);    // 右の子
            return this->mode.f(vl, vr);
        }
    }

    void propagate(const int k, const int len) {
        if (this->lazy[k] == this->mode.lazy_unit) {
            return;
        }

        if (len > 1) {
            this->lazy[k * 2 + 1] = this->mode.h(this->lazy[k * 2 + 1], this->lazy[k]);
            this->lazy[k * 2 + 2] = this->mode.h(this->lazy[k * 2 + 2], this->lazy[k]);
        }
        this->data[k] = this->mode.g(this->data[k], this->mode.p(this->lazy[k], len));
        this->lazy[k] = this->mode.lazy_unit;
    }
};

template<typename T>
Mode<T> range_summation_query_add() {
    return Mode<T>{
            [](T a, T b) { return a + b; },
            [](T a, T b) { return a + b; },
            [](T a, T b) { return a + b; },
            [](T a, int len) { return a * len; },
            0,
            0,
    };
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;

    Tree<LL> tree(N);
    vector<pair<LL, LL>> edge_2node(N - 1);
    vector<LL> edge_w(N - 1);
    FOR(i, 0, N - 1) {
        LL U, V, W;
        cin >> U >> V >> W;
        U--;
        V--;
        tree.add_undirected_edge(U, V, W);
        edge_2node[i] = {U, V};
        edge_w[i] = W;
    }

    TreeDistance<LL> td(tree);
    td.build(0);

    EulerTour<LL> et(tree);
    et.build(0);

    auto mode = range_summation_query_add<LL>();

    vector<LL> vv(et.tour.size());
    FOR(i, 0, LEN(et.tour)) {
        int u = et.tour[i];
        vv[i] = td.distance_from_root[u];
    }

    LazySegmentTree<LL> lst(vv, mode);

    vector<int> edge_node(N);
    FOR(i, 0, N - 1) {
        auto [u, v] = edge_2node[i];
        if (td.depth[u] > td.depth[v]) {
            edge_node[i] = u;
        }
        else {
            edge_node[i] = v;
        }
    }

    vector<LL> ans;
    int Q;
    cin >> Q;
    FOR(i, 0, Q) {
        int QUERY;
        cin >> QUERY;
        if (QUERY == 1) {
            LL I, W;
            cin >> I >> W;
            I--;

            int u = edge_node[I];
            LL moto_w = edge_w[I];

            auto p = et.range(u);
            lst.operation(p.first, p.second, W - moto_w);
            edge_w[I] = W;
        }
        else {
            int U, V;
            cin >> U >> V;
            U--;
            V--;

            int u = et.tour_idx(U);
            int v = et.tour_idx(V);
            int lca = et.tour_idx(td.lca(U, V));
            ans.emplace_back(lst.access(u) + lst.access(v) - 2 * lst.access(lca));
        }
    }

    print(ans);

    return 0;
}