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
#define FOR(i,a,n) for(int i=(a);i<(n); ++i)
#define FOE(i,a) for(auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define SUM(x) std::accumulate(ALL(x), 0LL)
#define MIN(v) *std::min_element(v.begin(), v.end())
#define MAX(v) *std::max_element(v.begin(), v.end())
#define EXIST(v,x) (std::find(v.begin(), v.end(), x) != v.end())
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

template<class T> inline std::vector<T> unique(std::vector<T> v) {
    sort(v.begin(), v.end());
    v.erase(unique(v.begin(), v.end()), v.end());
    return v;
}

long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}


bool is_power_of_two(long long x) {
    return !(x & (x - 1));
}


long long gcd(long long a, long long b) {
    if (b == 0) { return a; }
    return gcd(b, a % b);
}


long long gcd(std::vector<long long> &v) {
    long long ans = v[0];
    for (int i = 1; i < (int)v.size(); ++i) {
        ans = gcd(ans, v[i]);
    }
    return ans;
}


long long lcm(long long a, long long b) {
    long long g = gcd(a, b);
    return a / g * b;
}

const int INF = 1u << 30u;
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
const std::vector<int> dy2 = {0, 1}, dx2 = {1, 0};
const std::vector<int> dy4 = {0, 1, 0, -1}, dx4 = {1, 0, -1, 0};
const std::vector<int> dy8 = { 0, -1, 0, 1, 1, -1, -1, 1 }, dx8 = { 1, 0, -1, 0, 1, 1, -1, -1 };

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

// treeのdfsの行きがけ順
// ノードuの範囲は[in[u], out[u])
std::tuple<std::vector<int>, std::vector<int>, std::vector<int>> preorder_traversal(const int root, const Tree &tree) {
    const int n = tree.num_of_node;
    std::vector<int> preorder(n, -1), in(n, -1), out(n, -1);

    int no = 0;
    std::function<void(int, int)> dfs = [&](const int u, const int parent) {
        preorder[no] = u;
        in[u] = no++;
        for (const auto v : tree.tree.at(u)) {
            if (v != parent) {
                dfs(v, u);
            }
        }
        out[u] = no;
    };

    dfs(root, -1);

    return make_tuple(preorder, in, out);
}

template <class T=long long> class FenwickTree {
public:
    const int n;
    std::vector<T> v;

    FenwickTree(const int n) : n(n) {
        this->v.assign(n + 1, 0);
    }

    // O(log n)
    T access(const int i) {
        return this->sum(i, i + 1);
    }

    // sum(v[0, i))
    // O(log n)
    T sum(int i) {
        assert(0 <= i && i <= this->n);

        T s = 0;
        i -= 1;
        while (i >= 0) {
            s += this->v[i];
            i = (i & (i + 1)) - 1;
        }
        return s;
    }

    // sum(v[left, right))
    // O(log n)
    T sum(const int left, const int right) {
        assert(left <= right);
        return this->sum(right) - this->sum(left);
    }

    // v[i] += x
    // 0-origin
    // O(log n)
    void add(int i, T x) {
        assert(i < this->n);

        while (i < this->n) {
            this->v.at(i) += x;
            i |= i + 1;
        }
    }
};


using namespace std;

LL num_path(LL n) {
    return n * (n + 1) / 2;
}

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;
    auto C = make_v<int>(N);

    FOR(i, 0, N) {
        cin >> C[i];
        C[i]--;
    }

    Tree tree(N);
    FOR(i, 0, N - 1) {
        int A, B;
        cin >> A >> B;
        A--; B--;
        tree.add_undirected_edge(A, B);
    }

    std::vector<int> preorder, in, out;
    tie(preorder, in, out) = preorder_traversal(0, tree);

    // 各色の頂点
    auto color_nodes = make_v<int>(N, 0);
    FOR(u, 0, N) {
        color_nodes[C[u]].emplace_back(u);
    }
    // 各色を葉に近い順にソートする
    FOR(u, 0, N) {
        sort(ALL(color_nodes[u]), [&](int a, int b) {
            return in[a] > in[b];
        });
    }

    FenwickTree<LL> ft(N);
    FOR(i, 0, N) {
        ft.add(i, 1);
    }
    FOR(c, 0, N) {
        LL ans = num_path(N);
        auto log = make_v<pair<LL, LL>>(0);
        FOE(u, color_nodes[c]) {
            LL total = 1;
            FOE(v, tree.tree[u]) {
                if (in[v] < in[u]) {
                    continue;
                }
                LL num = ft.sum(in[v], out[v]);
                ans -= num_path(num);
                total += num;
            }

            ft.add(in[u], -total);
            log.emplace_back(make_pair(in[u], total));
        }

        ans -= num_path(ft.sum(0, N));
        FOE(p, log) {
            ft.add(p.first, p.second);
        }

        print(ans);
    }

    return 0;
}