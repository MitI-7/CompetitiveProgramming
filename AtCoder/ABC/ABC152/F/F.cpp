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
bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }
unsigned long long bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) {
    assert(b == 0 or b == 1);
    if (b == 0) { return bit & ~(1ull << i); }
    else        {return bit | (1ull << i); }
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


class Tree {
public:
    const int n;
    std::vector<std::vector<int>> tree;
    std::vector<int> parent;
    std::vector<vector<int>> children;

    Tree(int n) : n(n) {
        this->tree.resize(n);
        this->parent.resize(n);
        this->children.resize(n);
    }

    void add(int u, int v) {
        this->tree[u].emplace_back(v);
        this->tree[v].emplace_back(u);
    }

    void build(int root) {
        this->dfs(root, -1);
    }

private:
    void dfs(int u, int p) {
        this->parent[u] = p;
        for (int v : this->tree[u]) {
            if (v != p) {
                this->children[u].emplace_back(v);
                dfs(v, u);
            }
        }
    }

};

// fromからtoへいくルートを取得 O(n)
std::vector<int> route(const int from, const int to, const Tree &tree) {

    // get from -> to path
    std::unordered_map<int, int> prev;
    std::stack<int> nodes;
    nodes.push(to);
    while (not nodes.empty()) {
        const auto u = nodes.top(); nodes.pop();
        if (u == from) {
            break;
        }

        for (const auto v : tree.tree[u]) {
            if (prev.find(v) == prev.end()) {
                prev[v] = u;
                nodes.push(v);
            }
        }
    }

    std::vector<int> route = {from};
    int now = from;
    while (prev[now] != to) {
        now = prev[now];
        route.emplace_back(now);
    }
    route.emplace_back(to);

    return route;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    int N;
    cin >> N;
    auto tree = Tree(N);
    map<pair<int, int>, int> node_to_edge;
    FOR(i, 0, N - 1) {
        int A, B;
        cin >> A >> B;
        A--; B--;
        tree.add(A, B);
        node_to_edge[make_pair(A, B)] = i;
        node_to_edge[make_pair(B, A)] = i;
    }

    int M;
    cin >> M;

    auto edge_con = make_v<unsigned int>(N - 1);
    FOR(i, 0, M) {
        int U, V;
        cin >> U >> V;
        U--; V--;

        auto r = route(U, V, tree);
        FOR(j, 0, LEN(r) - 1) {
            int a = r[j];
            int b = r[j + 1];
            int e = node_to_edge[make_pair(a, b)];
            edge_con[e] = bit_set(edge_con[e], i, 1);
        }
    }

    auto dp = make_v<LL>(N, (1u << M) + 1);
    dp[0][0] = 1;
    FOR(e, 0, N - 1) {
        FOR(b, 0, (1u << M)) {
            // use
            dp[e + 1][b | edge_con[e]] += dp[e][b];

            // not use
            dp[e + 1][b] += dp[e][b];
        }
    }
    print(dp[N - 1][(1u << M) - 1]);

    return 0;
}