#include <iostream>
#include <array>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <math.h>
#include <string>
#include <climits>
#include <assert.h>
#include <iomanip>
#include <bitset>
#include <queue>
#include <deque>
#include <stack>
#include <functional>
#include <fstream>
#include <random>

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for(int i=(a);i<(n); ++i)
#define FOE(i, a) for(auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define SUM(x) std::accumulate(ALL(x), 0LL)
#define MIN(v) *std::min_element(v.begin(), v.end())
#define MAX(v) *std::max_element(v.begin(), v.end())
#define EXIST(v, x) (std::find(v.begin(), v.end(), x) != v.end())
#define BIT_COUNT(bit) (__builtin_popcount(bit))

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
template<class T> inline double manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }
template<typename T> T &chmin(T &a, const T &b) { return a = std::min(a, b); }
template<typename T> T &chmax(T &a, const T &b) { return a = std::max(a, b); }

template<class T> inline std::vector<T> unique(std::vector<T> v) {
    sort(v.begin(), v.end());
    v.erase(unique(v.begin(), v.end()), v.end());
    return v;
}

// 初項s交差d長さnの数列の和
long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}

// xが2の階乗かどうか判定
bool is_power_of_two(long long x) {
    return !(x & (x - 1));
}

long long gcd(long long a, long long b) {
    if (b == 0) { return a; }
    return gcd(b, a % b);
}

long long gcd(std::vector<long long> &v) {
    long long ans = v[0];
    for (int i = 1; i < (int) v.size(); ++i) {
        ans = gcd(ans, v[i]);
    }
    return ans;
}

long long lcm(long long a, long long b) {
    long long g = gcd(a, b);
    return a / g * b;
}

const int INF = 1u << 30u;  // 1,073,741,824
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
const std::vector<int> dy2 = {0, 1}, dx2 = {1, 0};
const std::vector<int> dy4 = {0, 1, 0, -1}, dx4 = {1, 0, -1, 0};
const std::vector<int> dy8 = {0, -1, 0, 1, 1, -1, -1, 1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};

using namespace std;

// 木上のクエリを処理
// ・作成(O(n log n))
// ・ノード間の距離(O(log n))
// ・直径・中心(O(log n))
// ・最小共通素性(O(log n))
// ・ノード間の最大の重み(O(log n))
class QueryOnTree {
private:
    const int n;

    int log_v = 0;
    std::vector<std::vector<int>> parent;        // 2^k個上の親
    std::vector<std::vector<int>> max_weight;    // 2^k個上の親までにでてくる最大の重み
    std::vector<int> depth;                      // 各頂点についての根からの深さ
    std::vector<long long> distance_from_root;   // 根からの距離
    bool done = false;

public:
    std::unordered_map<int, std::vector<std::pair<int, int>>> tree;

public:
    QueryOnTree(int n) : n(n) {
        this->log_v = int(log2(n)) + 1;
        this->parent.resize(log_v, vector<int>(n));
        this->max_weight.resize(log_v, vector<int>(n));
        this->depth.resize(n);
        this->distance_from_root.resize(n);
    }

    // 無向グラフの場合はu->vとv->uの両方をいれること
    void add_edge(int u, int v, int w) {
        assert(not done);
        tree[u].emplace_back(std::make_pair(v, w));
    }

    // O(n log n)
    void build(int root) {
        this->done = true;
        if (n == 0) {
            return ;
        }
        this->distance_from_root[root] = 0;

        dfs(root, -1, 0, 0);

        for (int k = 0; k + 1 < this->log_v; k++) {
            for (int u = 0; u < this->n; ++u) {
                if (parent[k][u] < 0) {
                    parent[k + 1][u] = -1;
                }
                else {
                    parent[k + 1][u] = parent[k][parent[k][u]]; // uの2^k個上のノードの2^k上のノードはuの2^(k+1)個上のノード
                    if (parent[k + 1][u] >= 0) {
                        max_weight[k + 1][u] = std::max(max_weight[k][u], max_weight[k][parent[k][u]]);
                    }
                }
            }
        }
    }

    // uとvの距離
    long long distance(int u, int v) {
        return distance_from_root[u] + distance_from_root[v] - 2 * distance_from_root[lca(u, v)];
    }

    // 木の直径
    long long diameter() {
        // node 0から一番遠いnode
        int u = 0;
        long long max_distance = -1;
        for (const auto &p : tree) {
            auto node = p.first;
            auto dist = this->distance(0, node);
            if (dist > max_distance) {
                max_distance = dist;
                u = node;
            }
        }

        // node uから一番遠いnode
        long long diameter = 0;
        for (const auto &p : tree) {
            auto node = p.first;
            auto dist = this->distance(u, node);
            if (dist > diameter) {
                diameter = dist;
            }
        }

        return diameter;
    }

    // 木の直径のパス
    std::vector<int> diameter_route() {
        // node 0から一番遠いnode
        int u = 0;
        long long max_distance = -1;
        for (int node = 0; node < this->n; ++node) {
            auto dist = this->distance(0, node);
            if (dist > max_distance) {
                max_distance = dist;
                u = node;
            }
        }

        // node uから一番遠いnode
        long long diameter = 0;
        int v = -1;
        for (int node = 0; node < this->n; ++node) {
            auto dist = this->distance(u, node);
            if (dist > diameter) {
                diameter = dist;
                v = node;
            }
        }

        return this->route(u, v);
    }

    // uからvへいくルートを取得 O(n)
    std::vector<int> route(const int u, const int v) {

        // get v -> u path
        std::unordered_map<int, int> prev;
        std::unordered_map<int, long long> dist;
        dist[v] = 0;
        std::stack<int> nodes;
        nodes.push(v);
        while (not nodes.empty()) {
            const auto node = nodes.top(); nodes.pop();
            if (node == u) {
                break;
            }

            for (const auto &p : tree[node]) {
                if (prev.find(p.first) == prev.end()) {
                    prev[p.first] = node;
                    dist[p.first] = dist[node] + p.second;
                    nodes.push(p.first);
                }
            }
        }

        std::vector<int> route = {u};
        int now = u;
        while (prev[now] != v) {
            now = prev[now];
            route.emplace_back(now);
        }
        route.emplace_back(v);

        return route;
    }

    // 木の中心
    int center() {
        std::vector<int> route = this->diameter_route();
        return route[route.size() / 2];
    }

    // uとvの間で出現する最大の重み
    int maximum_weight(int u, int v) {
        int lca = this->lca(u, v);
        return std::max(this->maximum_weight_ancestor(u, lca), this->maximum_weight_ancestor(v, lca));
    }

    // uとvの最近共通祖先(O(log n))
    int lca(int u, int v) {
        if (depth[u] > depth[v]) {
            std::swap(u, v);
        }
        for (int k = 0; k < this->log_v; ++k) {
            if ((depth[v] - depth[u]) >> k & 1) {
                v = parent[k][v];
            }
        }

        if (u == v) {
            return u;
        }

        for (int k = this->log_v - 1; k >= 0; --k) {
            if (parent[k][u] != parent[k][v]) {
                u = parent[k][u];
                v = parent[k][v];
            }
        }
        return parent[0][u];
    }

private:
    // 各頂点について，1つ上の親，1つ上の重み，根からの深さ，根からの距離を求める
    void dfs(int u, int p, int d, int w) {
        parent[0][u] = p;
        max_weight[0][u] = w;
        depth[u] = d;

        for (const auto &a : tree[u]) {
            int v = a.first;
            int dist = a.second;
            if (v != p) {
                distance_from_root[v] = distance_from_root[u] + dist;
                dfs(v, u, d + 1, dist);
            }
        }
    }

    // uとuの祖先の間の最大の重みを取得
    int maximum_weight_ancestor(int u, int ancestor) {
        int res = -INF;
        int d = depth[u] - depth[ancestor];
        for (int k = 0; k < log_v; k ++) {
            if ((d >> k) & 1) {
                res = std::max(res, max_weight[k][u]);
                u = parent[k][u];
            }
        }
        return res;
    }
};

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    LL N, U, V;
    cin >> N >> U >> V;
    U--; V--;

    QueryOnTree tree(N);
    FOR(i, 0, N - 1) {
        LL A, B;
        cin >> A >> B;
        A--; B--;
        tree.add_edge(A, B, 1);
        tree.add_edge(B, A, 1);
    }
    tree.build(0);

    LL ans = 0;
    FOR(a, 0, N) {
        if (tree.distance(U, a) < tree.distance(V, a)) {
            chmax(ans, tree.distance(V, a) - 1);
        }
    }
    print(ans);

    return 0;
}
