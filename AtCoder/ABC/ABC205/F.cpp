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
// clang-format on

using namespace std;

// #pragma once
// #include <cassert>
// #include <cmath>
// #include <numeric>
// #include <queue>
// #include <vector>

// capacity scaling + dinic
// O(EV log U)
template<typename T>
class Dinic {
public:
    struct Edge {
        const int from;
        const int to;
        T flow;
        const T cap;
        const int rev;

        Edge(const int from, const int to, const T flow, const T cap, const int rev) : from(from), to(to), flow(flow), cap(cap), rev(rev) {
            assert(this->cap >= 0);
        }

        T residual_capacity() const {
            return this->cap - this->flow;
        }
    };

    int num_nodes;
    int num_edges;
    std::vector<std::vector<Edge>> graph;
    std::vector<int> level;
    std::vector<int> current_edge;
    std::vector<std::pair<int, int>> edge_id_memo;

    Dinic() : num_nodes(0), num_edges(0) {}

    int add_node() {
        this->add_nodes(1);
        return this->num_nodes - 1;
    }

    std::vector<int> add_nodes(const int num) {
        std::vector<int> nodes(num);
        std::iota(nodes.begin(), nodes.end(), this->num_nodes);
        this->num_nodes += num;
        this->graph.resize(this->num_nodes);
        return nodes;
    }

    int add_directed_edge(const int from, const int to, const T cap) {
        assert(0 <= from and from < this->num_nodes and 0 <= to and to < this->num_nodes);
        assert(cap >= 0);
        this->graph[from].emplace_back(from, to, 0, cap, static_cast<int>(graph[to].size()));
        this->graph[to].emplace_back(to, from, cap, cap, static_cast<int>(graph[from].size()) - 1);
        this->edge_id_memo.emplace_back(from, static_cast<int>(this->graph[from].size()) - 1);
        return this->num_edges++;
    }

    Edge get_edge(const int edge_id) {
        const auto [u, i] = this->edge_id_memo[edge_id];
        return this->graph[u][i];
    }

    T solve(const int source, const int sink) {
        assert(source < this->num_nodes and sink < this->num_nodes);
        this->level.resize(this->num_nodes);
        this->current_edge.resize(this->num_nodes);

        T max_capacity = 0;
        for (int u = 0; u < this->num_nodes; ++u) {
            for (const auto &e: this->graph[u]) {
                max_capacity = std::max(max_capacity, e.cap);
            }
        }
        T delta = 1;
        while (delta <= max_capacity) {
            delta *= 2;
        }
        delta /= 2;

        T upper = 0;
        for (const auto &e: this->graph[source]) {
            upper += e.cap;
        }

        T flow = 0;
        while (delta > 0) {
            // solve maximum flow in delta-residual network
            while (true) {
                this->bfs(source, sink, delta);

                // no s-t path
                if (this->level[source] >= this->num_nodes) {
                    break;
                }

                fill(this->current_edge.begin(), this->current_edge.end(), 0);
                flow += dfs(source, sink, upper, delta);
            }
            delta /= 2;
        }

        return flow;
    }

    std::vector<bool> minimum_cut(const int source) {
        std::vector<bool> visited(this->num_nodes);
        std::queue<int> que;
        que.emplace(source);
        visited[source] = true;

        while (not que.empty()) {
            const auto u = que.front();
            que.pop();

            for (const auto &e: this->graph[u]) {
                if (not visited[e.to] and e.residual_capacity() != 0) {
                    visited[e.to] = true;
                    que.emplace(e.to);
                }
            }
        }

        return visited;
    }

private:
    void bfs(int source, int sink, T delta) {
        fill(this->level.begin(), this->level.end(), this->num_nodes);
        std::queue<int> que;
        this->level[sink] = 0;
        que.push(sink);
        while (not que.empty()) {
            auto v = que.front();
            que.pop();

            for (const auto &e: this->graph[v]) {
                // check e.to -> v
                if (e.flow >= delta and level[e.to] == this->num_nodes) {
                    this->level[e.to] = this->level[v] + 1;
                    if (e.to != source) {
                        que.push(e.to);
                    }
                }
            }
        }
    }

    T dfs(const int u, const int sink, T upper, T delta) {
        if (u == sink) {
            return upper;
        }

        T flow = 0;
        for (int &i = this->current_edge[u]; i < static_cast<int>(this->graph[u].size()); ++i) {
            auto &e = this->graph[u][i];
            const auto residual_capacity = e.residual_capacity();
            if (residual_capacity >= delta and this->level[u] > this->level[e.to]) {
                const auto d = dfs(e.to, sink, std::min(upper - flow, residual_capacity), delta);
                // update flow
                e.flow += d;
                this->graph[e.to][e.rev].flow -= d;

                flow += d;
                if (flow == upper or d == 0) {
                    return flow;
                }
            }
        }
        this->level[u] = this->num_nodes;

        return flow;
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int H, W, N;
    cin >> H >> W >> N;

    Dinic<int> dinic;
    const auto ys = dinic.add_nodes(H);
    const auto xs = dinic.add_nodes(W);
    const auto p1 = dinic.add_nodes(N);
    const auto p2 = dinic.add_nodes(N);
    const auto s = dinic.add_node();
    const auto t = dinic.add_node();

    FOR(y, 0, H) {
        dinic.add_directed_edge(s, ys[y], 1);
    }
    FOR(x, 0, W) {
        dinic.add_directed_edge(xs[x], t, 1);
    }
    FOR(i, 0, N) {
        dinic.add_directed_edge(p1[i], p2[i], 1);
    }

    FOR(i, 0, N) {
        int Y1, X1, Y2, X2;
        cin >> Y1 >> X1 >> Y2 >> X2;
        Y1--;
        X1--;
        Y2--;
        X2--;

        FOR(y, Y1, Y2 + 1) {
            dinic.add_directed_edge(ys[y], p1[i], 1);
        }
        FOR(x, X1, X2 + 1) {
            dinic.add_directed_edge(p2[i], xs[x], 1);
        }
    }

    print(dinic.solve(s, t));


    return 0;
}
