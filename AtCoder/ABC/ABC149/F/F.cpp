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

class Tree {
public:
    int num_of_node;
    std::vector<std::vector<int>> tree;
    std::vector<int> parent;
    std::vector<std::vector<int>> children;
    std::vector<int> weight;

    Tree() { }

    Tree(int num_of_node) {
        init(num_of_node);
    }

    void init(int _num_of_node) {
        this->num_of_node = _num_of_node;
        this->tree.resize(_num_of_node);
        this->parent.resize(_num_of_node, -1);
        this->children.resize(_num_of_node);
    }

    // u <-> v
    void add_undirected_edge(int u, int v) {
        this->tree[u].emplace_back(v);
        this->tree[v].emplace_back(u);
    }

    void remove_undirected_edge(int u, int v) {
        this->tree[u].erase(std::remove(tree[u].begin(), tree[u].end(), v), tree[u].end());
        this->tree[v].erase(std::remove(tree[v].begin(), tree[v].end(), u), tree[v].end());
    }

    // u -> v
    void add_directed_edge(int u, int v) {
        this->parent[v] = u;
        this->children[u].emplace_back(v);
    }

    void remove_directed_edge(int u, int v) {
        this->parent[v] = -1;
        this->tree[u].erase(std::remove(tree[u].begin(), tree[u].end(), v), tree[u].end());
    }

    // 無向木を有向木にする
    bool build_directed_tree(const int root) {
        this->parent.resize(this->num_of_node, -1);
        this->children.resize(this->num_of_node);

        std::vector<bool> used(this->num_of_node);
        return this->dfs(root, -1, used);
    }

private:
    bool dfs(const int u, const int p, std::vector<bool> &used) {
        this->parent[u] = p;
        used[u] = true;

        bool ok = true;
        for (int v : this->tree[u]) {
            if (v != p) {
                if (used[v]) {
                    return false;
                }
                this->children[u].emplace_back(v);
                ok &= dfs(v, u, used);
            }
        }

        return ok;
    }
};

// 各ノードの子供の総数を取得 O(NM)
// num_children_dfs(root, num_children, tree)
long long num_children_dfs(int u, std::vector<long long> &num_children, Tree &tree) {
    long long total = 1;
    for (auto v : tree.children[u]) {
        total += num_children_dfs(v, num_children, tree);
    }

    return num_children[u] = total;
}

template<int mod> struct mint {
    long long x;
    mint(long long x = 0) : x(x % mod) {
    }

    mint& operator+=(const mint a) {
        if ((x += a.x) >= mod) {
            x -= mod;
        }
        return *this;
    }
    mint& operator-=(const mint a) {
        if ((x += mod-a.x) >= mod) {
            x -= mod;
        }
        return *this;
    }
    mint& operator*=(const mint a) {
        (x *= a.x) %= mod;
        return *this;
    }
    mint operator+(const mint a) const {
        mint res(*this);
        return res+=a;
    }
    mint operator-(const mint a) const {
        mint res(*this);
        return res-=a;
    }
    mint operator*(const mint a) const {
        mint res(*this);
        return res*=a;
    }
    mint pow(long long t) const {
        if (!t) {
            return 1;
        }
        mint a = pow(t>>1);
        a *= a;
        if (t&1) {
            a *= *this;
        }
        return a;
    }

    // for prime mod
    mint inv() const {
        return pow(mod-2);
    }
    mint& operator/=(const mint a) {
        return (*this) *= a.inv();
    }
    mint operator/(const mint a) const {
        mint res(*this);
        return res/=a;
    }
};

// modがでかいときはoverflowに注意
long long powmod(long long base, long long exp, long long mod) {
    long long x = 1, y = base;
    while (exp > 0) {
        if (exp % 2 == 1) {
            x = (x * y) % mod;
        }
        y = (y * y) % mod;
        exp /= 2;
    }

    return int(x % mod);
}

const int MOD = 1000000000 + 7;

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    LL N;
    cin >> N;

    Tree tree(N);
    FOR(i, 0, N - 1) {
        LL A, B;
        cin >> A >> B;
        A--; B--;
        tree.add_undirected_edge(A, B);
    }
    tree.build_directed_tree(0);

    auto num_children = make_v<LL>(N);
    num_children_dfs(0, num_children, tree);

    mint<MOD> ans = 0;
    const mint<MOD> t = powmod(2, N - 1, MOD);
    FOR(u, 0, N) {
        mint<MOD> base = 0;
        // uが白であるような場合の数
        LL num = 0;
        FOE(v, tree.children[u]) {
            num += num_children[v];
            base += (powmod(2, num_children[v], MOD) - 1);      // v方向に黒がある
        }
        base += (powmod(2, (N - num - 1), MOD) - 1);
        base += 1;   // 全部白

        ans += (t - base);
    }

    ans /= powmod(2, N, MOD);
    print(ans.x);

    return 0;
}
