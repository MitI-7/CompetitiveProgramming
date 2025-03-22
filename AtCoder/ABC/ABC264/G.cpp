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
// #include <iostream>
// #include <unordered_map>
// #include <vector>

template<typename T>
class Edge {
public:
    int from;
    int to;
    T w;
    int no;

    Edge() : from(-1), to(-1), w(-1), no(-1) {}

    Edge(const int from, const int to, const T w = 1, const int no = -1) : from(from), to(to), w(w), no(no) {}
};

template<typename T = int>
class Graph {
public:
    const int num_nodes;
    int num_edges;
    std::vector<std::vector<Edge<T>>> graph;
    std::unordered_map<int, std::pair<int, int>> no_edge;

    explicit Graph(const int num_nodes) : num_nodes(num_nodes), num_edges(0) {
        this->graph.resize(num_nodes);
    }

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

    Edge<T> &get_edge(const int no) {
        const auto [u, i] = this->no_edge[no];
        return this->graph[u][i];
    }

    std::vector<Edge<T>> &operator[](const int u) {
        return this->graph[u];
    }
};

// #include <functional>
// #include <limits>
// #include <queue>
// #include <vector>
// #include "library/graph/Graph.hpp"

/**
 * start から他のすべての node への最短距離をもとめる
 * 到達できない node の距離は infinity とし，負の閉路がある場合は空を返す
 * start から到達できないような負の閉路は無視されるが、goal に到達できない負の閉路がある場合も空が返ることに注意
 * goal に到達できない負の閉路を無視したい場合は，goal に到達できないようなノードに入る辺を除去しておけばいい
 * O(|V||E|)
 */
template<typename T>
std::pair<std::vector<T>, std::vector<Edge<T>>> bellman_ford(const int start, Graph<T> &graph, const T infinity = std::numeric_limits<T>::max() / 3) {
    const int num_nodes = graph.num_nodes;
    std::vector<T> distance(num_nodes, infinity);
    distance[start] = 0;
    std::vector<Edge<T>> prev_edge(graph.num_nodes); // 経路復元用

    int i;
    for (i = 0; i < num_nodes; ++i) {
        bool update = false;
        for (int u = 0; u < num_nodes; ++u) {
            for (const auto &edge: graph[u]) {
                if (distance[u] != infinity and distance[edge.to] > distance[u] + edge.w) {
                    distance[edge.to] = distance[u] + edge.w;
                    prev_edge[edge.to] = edge;
                    update = true;
                }
            }
        }
        if (not update) {
            break;
        }
    }

    if (i == num_nodes) {
        return {{}, {}};
    } else {
        return {distance, prev_edge};
    }
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;

    map<string, LL> m;
    FOR(i, 0, N) {
        string T;
        LL P;
        cin >> T >> P;
        m[T] += P;
    }

    map<string, int> nodes;
    const string s = "abcdefghijklmnopqrstuvwxyz";

    nodes[string()] = LEN(nodes);
    FOR(i, 0, LEN(s)) {
        nodes[string() + s[i]] = LEN(nodes);
    }
    FOR(i, 0, LEN(s)) {
        FOR(j, 0, LEN(s)) {
            nodes[string() + s[i] + s[j]] = LEN(nodes);
        }
    }

    map<int, string> rev;
    FOE(p, nodes) {
        rev[p.second] = p.first;
    }

    Graph<LL> graph(LEN(nodes));
    FOE(p, nodes) {
        const int u = nodes[p.first];
        FOE(c, s) {
            string v_s = p.first + c;
            if (LEN(v_s) >= 3) {
                v_s.erase(v_s.begin());
            }
            assert(LEN(v_s) <= 2);
            const int v = nodes[v_s];
            assert(v != 0);

            string t = p.first + c;
            LL cost = m[t];
            FOR(_, 0, 2) {
                if (LEN(t) > 0) {
                    t.erase(t.begin());
                    cost += m[t];
                }
            }
            graph.add_directed_edge(u, v, -cost);
        }
    }

    auto [d, pre] = bellman_ford(nodes[""], graph, LINF);
    if (LEN(d) == 0) {
        print("Infinity");
    } else {
        LL ans = -LINF;
        FOR(u, 1, LEN(d)) {
            if (d[u] != LINF) {
                chmax(ans, -d[u]);
            }
        }
        print(ans);
    }

    return 0;
}
