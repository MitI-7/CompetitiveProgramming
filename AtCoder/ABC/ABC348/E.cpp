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

#include <cassert>
#include <functional>
#include <stack>
#include <vector>

template<typename W>
class Edge {
public:
    int to;
    W w;
    int rev;
    int no;

    Edge() : to(-1), w(-1), rev(-1), no(-1) {}

    Edge(int to, W w, int rev, int no = -1) : to(to), w(w), rev(rev), no(no) {
    }
};

// モノイドを乗せることができる
// 結合則: a * (b * c) = (a * b) * c
// 単位元: e * a = a * e = a
template<class T, typename W, T (*marge)(T, T), T (*add_node)(T, int), T (*add_edge)(T, Edge<W>), T (*unit)()>
class ReRooting {
public:
    const int num_nodes;

private:
    std::vector<std::vector<Edge<W>>> graph;

    std::vector<std::vector<T>> dp;// dp[u][i] = 頂点 u の i 番目の子供を部分木の根とした答え
    std::vector<T> ans;

    bool initialized;

public:
    explicit ReRooting(const int num_nodes) : num_nodes(num_nodes), graph(num_nodes), dp(num_nodes), ans(num_nodes), initialized(false) {
    }

    void add_undirected_edge(const int u, const int v, const W w = 1) {
        assert(not this->initialized);
        assert(u != v);
        const int rev_u = this->graph[v].size();
        const int rev_v = this->graph[u].size();
        this->graph[u].emplace_back(Edge(v, w, rev_u));
        this->graph[v].emplace_back(Edge(u, w, rev_v));
    }

    T query(const int u) const {
        assert(this->initialized);
        assert(0 <= u and u < this->num_nodes);
        return this->ans[u];
    }

    void build() {
        this->initialized = true;

        for (int i = 0; i < (int) this->graph.size(); i++) {
            this->dp[i].resize(this->graph[i].size());
        }

        // 頂点が 1 個しなかない
        if (this->num_nodes == 1) {
            this->ans[0] = add_node(unit(), 0);
            return;
        }

        std::vector<int> parents(num_nodes);
        std::vector<int> order;

        // 頂点 0 を根とした dfs 順と各ノードの親を求める
        {
            std::stack<int> stack;
            stack.push(0);
            parents[0] = -1;
            while (not stack.empty()) {
                const auto u = stack.top();
                stack.pop();
                order.emplace_back(u);
                for (const auto e: this->graph[u]) {
                    if (e.to == parents[u]) {
                        continue;
                    }
                    stack.push(e.to);
                    parents[e.to] = u;
                }
            }
        }

        // 葉から根へ部分木の値を求めていく
        for (int i = (int) order.size() - 1; i >= 1; --i) {
            const auto u = order[i];
            const auto parent = parents[u];

            // u の子供達の結果をまとめる
            T accum = unit();
            int rev = -1;
            for (int j = 0; j < (int) this->graph[u].size(); ++j) {
                const auto &edge = this->graph[u][j];
                if (edge.to == parent) {
                    rev = edge.rev;
                    continue;
                }
                accum = marge(accum, add_edge(this->dp[u][j], edge));
            }
            assert(rev != -1);

            // u を部分木の根としたときの答えを求める
            this->dp[parent][rev] = add_node(accum, u);
            assert(this->graph[parent][rev].to == u);
        }

        // u を木の根としたときの値を求める
        for (const auto u: order) {

            // 右ろからの累積和を求める(dp[u] の先頭は入っていない)
            std::vector<T> accums_left(this->graph[u].size());
            accums_left[accums_left.size() - 1] = unit();
            for (int j = (int) accums_left.size() - 1; j >= 1; --j) {
                const auto &edge = this->graph[u][j];
                auto val = add_edge(this->dp[u][j], edge);
                accums_left[j - 1] = marge(val, accums_left[j]);
            }

            // 左からの累積和を求める
            T accum = unit();
            for (int j = 0; j < (int) accums_left.size(); j++) {
                const auto &edge = graph[u][j];
                // j が入っていない
                this->dp[edge.to][edge.rev] = add_node(marge(accum, accums_left[j]), u);
                const auto val = add_edge(this->dp[u][j], edge);
                accum = marge(accum, val);
            }

            this->ans[u] = add_node(accum, u);
        }
    }
};

vector<LL> C;


// 累積 accum と t を結合する関数
// （子供達の結合のみ考慮し，親に結合するときのことは考えないことに注意）
template<typename T>
T merge(const T accum, const T t) {
    return {accum.first + t.first, accum.second + t.second};
}

// 子供達の結果と頂点 u を結合する関数
template<typename T>
T add_node(const T accum, const int u) {
    return {accum.first + accum.second, accum.second + C[u]};
}

// 結果 t に 辺 e を影響させる
template<typename T, typename W>
T add_edge(const T t, Edge<W> e) {
    return t;
}

// 単位元
template<typename T>
T unit() {
    return {0, 0};
}


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;

    ReRooting<pair<LL, LL>, LL, merge, add_node, add_edge, unit> rr(N);
    FOR(i, 0, N - 1) {
        int A, B;
        cin >> A >> B;
        A--;
        B--;
        rr.add_undirected_edge(A, B, 1);
    }

    C = make_v<LL>(N);
    FOR(i, 0, N) {
        cin >> C[i];
    }

    rr.build();

    LL ans = 9e18;
    FOR(u, 0, N) {
        chmin(ans, rr.query(u).first);
    }
    print(ans);

    return 0;
}
