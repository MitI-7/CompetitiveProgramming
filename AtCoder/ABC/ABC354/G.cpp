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
// 2次元配列上での移動．右，下，左，上，右上，右下，左下，左上
const std::vector<int> dy8 = {0, 1, 0, -1, -1, 1, 1, -1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};
// @formatter:on

using namespace std;

// capacity scaling + dinic
// O(EV log U)
template <typename T>
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
            for (const auto& e : this->graph[u]) {
                max_capacity = std::max(max_capacity, e.cap);
            }
        }
        T delta = 1;
        while (delta <= max_capacity) {
            delta *= 2;
        }
        delta /= 2;

        T upper = 0;
        for (const auto& e : this->graph[source]) {
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

            for (const auto& e : this->graph[u]) {
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

            for (const auto& e : this->graph[v]) {
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
        for (int& i = this->current_edge[u]; i < static_cast<int>(this->graph[u].size()); ++i) {
            auto& e = this->graph[u][i];
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

    int N;
    cin >> N;

    map<string, int> m;
    {
        vector<string> S(N);
        FOR(i, 0, N) {
            cin >> S[i];
        }
        vector<int> A(N);
        FOR(i, 0, N) {
            cin >> A[i];
        }
        FOR(i, 0, N) {
            chmax(m[S[i]], A[i]);
        }
    }

    vector<string> S;
    vector<int> A;
    for (const auto& [s, a] : m) {
        S.emplace_back(s);
        A.emplace_back(a);
    }

    N = LEN(S);
    Dinic<LL> dinic;
    vector<int> in, out;
    FOR(i, 0, N) {
        in.emplace_back(dinic.add_node());
        out.emplace_back(dinic.add_node());
    }

    FOR(i, 0, N) {
        FOR(j, 0, N) {
            if (i == j) {
                continue;
            }

            // S[i] は S[j] を含む
            if (S[i].find(S[j]) != string::npos) {
                dinic.add_directed_edge(in[i], out[j], INF);
            }
        }
    }

    int s = dinic.add_node();
    int t = dinic.add_node();
    FOR(i, 0, N) {
        dinic.add_directed_edge(s, in[i], A[i]);
        dinic.add_directed_edge(out[i], t, A[i]);
    }

    LL ans = 0;
    FOR(i, 0, N) {
        ans += A[i];
    }
    ans -= dinic.solve(s, t);
    print(ans);

    return 0;
}
