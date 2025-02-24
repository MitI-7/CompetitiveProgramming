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

template <typename T>
class Edge {
public:
    int from;
    int to;
    T w;
    int no;

    Edge() : from(-1), to(-1), w(-1), no(-1) {}

    Edge(const int from, const int to, const T w = 1, const int no = -1) : from(from), to(to), w(w), no(no) {}
};

template <typename T = int>
class Graph {
public:
    const int num_nodes;
    int num_edges;
    std::vector<std::vector<Edge<T>>> graph;
    std::unordered_map<int, std::pair<int, int>> no_edge;

    explicit Graph(const int num_nodes) : num_nodes(num_nodes), num_edges(0) { this->graph.resize(num_nodes); }

    void add_directed_edge(const int u, const int v, const T w = 1, const int no = -1) {
        this->no_edge[no] = {u, this->graph[u].size()};
        this->graph[u].emplace_back(Edge(u, v, w, no));
        ++this->num_edges;
    }

    void add_undirected_edge(const int u, const int v, const T w = 1, const int no = -1) {
        this->graph[u].emplace_back(Edge(u, v, w, no));
        this->graph[v].emplace_back(Edge(v, u, w, no));
        this->num_edges += 2;
    }

    Edge<T>& get_edge(const int no) {
        const auto [u, i] = this->no_edge[no];
        return this->graph[u][i];
    }

    std::vector<Edge<T>>& operator[](const int u) { return this->graph[u]; }
};

// 強連結成分分解(一意に定まりDAGになる)
class StronglyConnectedComponents {
public:
    int num_component = -1;

private:
    const int num_nodes;
    std::vector<std::vector<int>> graph;
    std::vector<std::vector<int>> rev_graph;
    std::vector<int> node_component; // 元のノード番号 -> コンポーネントのノード番号
    std::vector<std::unordered_set<int>> component_nodes; // コンポーネントのノード番号 -> 元のノードの集合

public:
    StronglyConnectedComponents(const int num_nodes) :
        num_nodes(num_nodes), graph(num_nodes), rev_graph(num_nodes), node_component(num_nodes) {}

    void add_directed_edge(const int from, const int to) {
        this->graph[from].emplace_back(to);
        this->rev_graph[to].emplace_back(from);
    }

    // ノードuがどのコンポーネントに所属するか
    [[nodiscard]] int get_component_no(const int u) const { return this->node_component[u]; }

    // コンポーネントnoに所属するノードのsetを返す
    // make_new_graph()を実行する必要がある
    [[nodiscard]] std::unordered_set<int> get_nodes(const int component_no) const {
        return this->component_nodes[component_no];
    }

    // O(|V| + |E|)
    // コンポーネント数を返す
    int build() {
        std::vector<int> vs; // 帰りがけ順の並び
        {
            std::vector<bool> used(this->num_nodes);
            for (int u = 0; u < this->num_nodes; ++u) {
                if (not used[u]) {
                    this->dfs(u, used, vs);
                }
            }
        }

        std::vector<bool> used(this->num_nodes);
        this->num_component = 0;
        for (int i = int(vs.size()) - 1; i >= 0; --i) {
            if (not used[vs[i]]) {
                this->rdfs(vs[i], this->num_component++, used);
            }
        }

        return this->num_component;
    }

    // 強連結成分をひとつのノードにまとめたグラフを返す
    // トポロジカル順
    Graph<int> make_new_graph() {
        Graph<int> dag(this->num_component);
        this->component_nodes.resize(this->num_component);

        std::set<std::pair<int, int>> used;

        for (int u = 0; u < this->num_nodes; ++u) {
            const int u_component_no = this->node_component[u];
            this->component_nodes[u_component_no].insert(u);

            for (const auto v : this->graph[u]) {
                const int v_component_no = this->node_component[v];
                this->component_nodes[v_component_no].insert(v);
                if (u_component_no == v_component_no) {
                    continue;
                }

                if (not used.contains({u_component_no, v_component_no})) {
                    assert(u_component_no < v_component_no);
                    dag.add_directed_edge(u_component_no, v_component_no);
                    used.insert({u_component_no, v_component_no});
                }
            }
        }

        return dag;
    }

private:
    void dfs(const int u, std::vector<bool>& used, std::vector<int>& vs) {
        used[u] = true;
        for (const int v : this->graph[u]) {
            if (not used[v]) {
                dfs(v, used, vs);
            }
        }
        vs.emplace_back(u);
    }

    void rdfs(const int v, const int component_no, std::vector<bool>& used) {
        used[v] = true;
        this->node_component[v] = component_no;
        for (const int u : this->rev_graph[v]) {
            if (not used[u]) {
                this->rdfs(u, component_no, used);
            }
        }
    }
};


template<int mod>
struct mint {
    long long x;

    mint(long long x = 0) : x((x % mod + mod) % mod) {
    }

    mint &operator+=(const mint a) {
        if ((x += a.x) >= mod) {
            x -= mod;
        }
        return *this;
    }

    mint &operator-=(const mint a) {
        if ((x += mod - a.x) >= mod) {
            x -= mod;
        }
        return *this;
    }

    mint &operator*=(const mint a) {
        (x *= a.x) %= mod;
        return *this;
    }

    mint operator+(const mint a) const {
        mint res(*this);
        return res += a;
    }

    mint operator-(const mint a) const {
        mint res(*this);
        return res -= a;
    }

    mint operator*(const mint a) const {
        mint res(*this);
        return res *= a;
    }

    mint pow(long long t) const {
        if (!t) {
            return 1;
        }
        mint a = pow(t >> 1);
        a *= a;
        if (t & 1) {
            a *= *this;
        }
        return a;
    }

    // mod が素数のときのみ利用可能
    mint inv() const {
        return pow(mod - 2);
    }

    mint &operator/=(const mint a) {
        return (*this) *= a.inv();
    }

    mint operator/(const mint a) const {
        mint res(*this);
        return res /= a;
    }

    bool operator==(const mint a) const {
        return this->x == a.x;
    }

    friend std::ostream &operator<<(std::ostream &os, const mint &obj) {
        os << obj.x;
        return os;
    }
};

const int MOD = 998244353;
vector<vector<mint<MOD>>> dp;

void dfs(int u, int p, vector<vector<mint<MOD>>> &dp, int M, vector<vector<int>> &tree) {
    FOE(v, tree[u]) {
        if (v == p) {
            continue;
        }
        dfs(v, u, dp, M, tree);
        mint<MOD> ans = 0;
        FOR(k, 0, M) {
            ans += dp[v][k];
            dp[u][k] *= ans;
        }
    }
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, M;
    cin >> N >> M;
    vector<int> A(N);
    FOR(i, 0, N) {
        cin >> A[i];
        A[i]--;
    }

    StronglyConnectedComponents scc(N);
    FOR(i, 0, N) {
        scc.add_directed_edge(i, A[i]);
    }
    scc.build();
    auto g = scc.make_new_graph();

    auto tree = make_v<int>(g.num_nodes, 0);
    vector<int> out_deg(g.num_nodes);
    FOR(u, 0, g.num_nodes) {
        FOE(e, g[u]) {
            tree[u].emplace_back(e.to);
            tree[e.to].emplace_back(u);
            out_deg[u]++;
        }
    }

    mint<MOD> ans = 1;
    // dp[u][i] = uを根とする部分木で，uがiのときの場合の数
    vector dp(g.num_nodes, vector<mint<MOD>>(M, 1));

    FOR(u, 0, g.num_nodes) {
        if (out_deg[u] == 0) {
            dfs(u, -1, dp, M, tree);
            mint<MOD> t = 0;
            FOR(i, 0, M) {
                t += dp[u][i];
            }
            ans *= t;
        }
    }
    print(ans);

    return 0;
}
