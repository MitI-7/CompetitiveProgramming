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
        this->num_edges += 1;
    }

    Edge<T>& get_edge(const int no) {
        const auto [u, i] = this->no_edge[no];
        return this->graph[u][i];
    }

    std::vector<Edge<T>>& operator[](const int u) { return this->graph[u]; }
};

template<typename T>
std::pair<std::vector<T>, std::vector<Edge<T>>> dijkstra(const int s, const Graph<T> &graph, const int ng) {

    // [(最短距離, node番号)]のque (距離が近い順にとりだす)
    std::priority_queue<std::pair<T, int>, std::vector<std::pair<T, int>>, std::greater<>> que;
    que.push({0, s});

    std::vector<Edge<T>> prev_edge(graph.num_nodes);       // 経路復元用
    std::vector<bool> seen(graph.num_nodes);
    std::vector<T> distance(graph.num_nodes, LINF);   // startからの距離
    distance[s] = 0;

    while (not que.empty()) {
        const auto [now_dist, u] = que.top();
        que.pop();
        if (seen[u]) {
            continue;
        }
        seen[u] = true;

        for (auto edge: graph.graph[u]) {
            if (edge.no == ng) {
                continue;
            }
            const auto new_dist = now_dist + edge.w;
            if (new_dist < distance[edge.to]) {
                prev_edge[edge.to] = edge;
                distance[edge.to] = new_dist;
                que.push({new_dist, edge.to});
            }
        }
    }

    return {distance, prev_edge};
}

// グラフの橋(削除するとグラフの連結成分の数が増える辺)を検出する．
class BridgeDetection {
    int num_nodes;
    std::vector<std::vector<int>> graph;
    std::vector<int> state;
    std::vector<int> val;
    std::vector<int> color;

public:
    std::set<std::pair<int, int>> bridge_set;

    BridgeDetection(const int num_nodes) : num_nodes(num_nodes) {
        this->graph.resize(num_nodes);
        this->state.resize(num_nodes);
        this->val.resize(num_nodes);
        this->color.resize(num_nodes);
        for (int u = 0; u < this->num_nodes; ++u) {
            color[u] = -1;
        }
    }

    // 非連結，自己ループ，多重辺も可
    void add_undirected_edge(const int u, const int v) {
        this->graph[u].emplace_back(v);
        this->graph[v].emplace_back(u);
    }

    // O(|V| + |E|)
    void build() {
        // 連結成分ごとに同じ色を塗る
        int c = 0;
        for (int u = 0; u < this->num_nodes; ++u) {
            if (color[u] == -1) {
                dfs2(u, c);
                c++;
            }
        }

        std::vector<bool> used_color(c);

        for (int u = 0; u < this->num_nodes; ++u) {
            if (not used_color[color[u]]) {
                this->dfs(u, -1);
                used_color[color[u]] = true;
            }
        }
    }

private:
    int dfs(const int u, const int pre) {
        int res = 0;
        int count = 0;
        this->state[u] = 1;// searching
        for (int v: this->graph[u]) {
            if (v == u) {
                continue;
            }
            if (v == pre) {
                if (count > 0) {
                    // (pre, u): multiple edges
                    res += 1;
                    this->val[v] += 1;
                }
                ++count;
                continue;
            }
            if (not this->state[v]) {
                res += dfs(v, u);
            } else if (this->state[v] == 1) {
                res += 1;
                this->val[v] += 1;
            }
        }
        this->state[u] = 2;// searched
        res -= this->val[u];

        if (pre != -1 and res == 0) {
            if (pre < u) {
                this->bridge_set.insert(std::make_pair(pre, u));
            } else {
                this->bridge_set.insert(std::make_pair(u, pre));
            }
        }

        return res;
    }

    void dfs2(int u, int c) {
        this->color[u] = c;
        for (int v: this->graph[u]) {
            if (this->color[v] == -1) {
                dfs2(v, c);
            }
        }
    }
};

vector<string> solve(Graph<LL> &graph) {
    int N = graph.num_nodes;
    int M = graph.num_edges;

    vector<tuple<int, int, int>> edges(M);
    FOR(u, 0, N) {
        FOE(e, graph.graph[u]) {
            edges[e.no] = {e.from, e.to, e.w};
        }
    }

    auto [d1, prev_edge] = dijkstra(0, graph, -1);
    auto [d2, _] = dijkstra(N - 1, graph, -1);

    BridgeDetection bd(N);
    for (auto [u, v, w]: edges) {
        if (d1[u] > d1[v]) {
            swap(u, v);
        }
        if (d1[u] + w + d2[v] == d1[N - 1]) {
            bd.add_undirected_edge(u, v);
        }
    }
    bd.build();

    vector<string> ans(M, "No");
    FOR(i, 0, M) {
        const auto& [u, v, _] = edges[i];
        if (bd.bridge_set.contains({u, v}) or bd.bridge_set.contains({v, u})) {
            ans[i] = "Yes";
        }
    }

    return ans;
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, M;
    cin >> N >> M;
    Graph<LL> graph(N);
    FOR(i, 0, M) {
        int A, B, C;
        cin >> A >> B >> C;
        A--;
        B--;
        graph.add_undirected_edge(A, B, C, i);
    }

    auto ans = solve(graph);
    print(ans);

    return 0;
}
