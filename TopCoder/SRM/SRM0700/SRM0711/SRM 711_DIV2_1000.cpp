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

template<typename T>
std::vector<T> make_v(size_t a) { return std::vector<T>(a); }

template<typename T, typename... Ts>
auto make_v(size_t a, Ts... ts) { return std::vector<decltype(make_v<T>(ts...))>(a, make_v<T>(ts...)); }    // C++14
template<typename T, typename V>
typename std::enable_if<std::is_class<T>::value == 0>::type fill_v(T &t, const V &v) { t = v; }

template<typename T, typename V>
typename std::enable_if<std::is_class<T>::value != 0>::type fill_v(T &t, const V &v) { for (auto &e:t) fill_v(e, v); }

template<class T>
inline T ceil(T a, T b) { return (a + b - 1) / b; }

void print() { std::cout << std::endl; }

template<class Head, class... Tail>
void print(Head &&head, Tail &&... tail) {
    std::cout << head;
    if (sizeof...(tail) != 0) { std::cout << " "; }
    print(std::forward<Tail>(tail)...);
}

template<class T>
void print(std::vector<T> &v) {
    for (auto &a : v) {
        std::cout << a;
        if (&a != &v.back()) { std::cout << " "; }
    }
    std::cout << std::endl;
}

template<class T>
void print(std::vector<std::vector<T>> &vv) { for (auto &v : vv) { print(v); }}

void debug() { std::cerr << std::endl; }

template<class Head, class... Tail>
void debug(Head &&head, Tail &&... tail) {
    std::cerr << head;
    if (sizeof...(tail) != 0) { std::cerr << " "; }
    print(std::forward<Tail>(tail)...);
}

template<class T>
void debug(std::vector<T> &v) {
    for (auto &a : v) {
        std::cerr << a;
        if (&a != &v.back()) { std::cerr << " "; }
    }
    std::cerr << std::endl;
}

template<class T>
void debug(std::vector<std::vector<T>> &vv) { for (auto &v : vv) { print(v); }}

inline bool inside(long long y, long long x, long long H, long long W) { return 0 <= y and y < H and 0 <= x and x < W; }

template<class T>
inline double euclidean_distance(T y1, T x1, T y2, T x2) { return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)); }

template<class T>
inline double manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }

template<typename T>
T &chmin(T &a, const T &b) { return a = std::min(a, b); }

template<typename T>
T &chmax(T &a, const T &b) { return a = std::max(a, b); }

bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }

unsigned long long bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) {
    assert(b == 0 or b == 1);
    if (b == 0) { return bit & ~(1ull << i); }
    else { return bit | (1ull << i); }
}

template<class T>
inline std::vector<T> unique(std::vector<T> v) {
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
    for (int i = 1; i < (int) v.size(); ++i) {
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
const std::vector<int> dy8 = {0, -1, 0, 1, 1, -1, -1, 1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};

using namespace std;

static const int MOD = 1000000007;

template<int mod>
struct mint {
    long long x;

    mint(long long x = 0) : x(x % mod) {
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

    // for prime mod
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
};

class UnionFind {
public:
    const int n;        // 要素の個数
    int set_size;       // 集合の個数
private:
    std::vector<int> parent;	// 親の番号(親だった場合は-(その集合のサイズ))

public:
    UnionFind(int n) : n(n), set_size(n), parent(n, -1) {}

    // xとyが同じ集合に属するか
    bool is_same_set(int x, int y) {
        return find_root(x) == find_root(y);
    }

    // xとyの属する集合を併合
    void union_set(int x, int y) {
        x = find_root(x);
        y = find_root(y);
        if (x == y) {
            return;
        }
        if (parent[x] > parent[y]) {
            swap(x, y);
        }

		// 小さい方(x)に大きい方(y)をくっつける
		// 両方ともrootなので-(集合のサイズ)が入っている
        parent[x] += parent[y];
        // yの親をxにする
        parent[y] = x;
        set_size--;
    }

    // xの属する集合の要素数
    int size(int x) {
        return (-parent[find_root(x)]);
    }

private:
    // 木の根を求める
    int find_root(int x) {
        if (parent[x] < 0) {
            return x;
        }
        else {
            return parent[x] = find_root(parent[x]);
        }
    }
};

class Tree {
public:
    int num_node;
    std::vector<std::vector<int>> tree;
    std::vector<std::pair<int, int>> edge_nodes;
    std::map<pair<int, int>, int> nodes_edge;

    Tree() {
    }

    Tree(int num_node) {
        init(num_node);
    }

    void init(const int _num_node) {
        this->num_node = _num_node;
        this->tree.resize(_num_node);
        this->edge_nodes.resize(_num_node - 1);
    }

    void add_undirected_edge(const int u, const int v, const int edge_no) {
        this->tree[u].emplace_back(v);
        this->tree[v].emplace_back(u);
        edge_nodes[edge_no] = std::make_pair(u, v);
        nodes_edge[make_pair(u, v)] = edge_no;
        nodes_edge[make_pair(v, u)] = edge_no;
    }

    void add_directed_edge(const int u, const int v, const int edge_no) {
        this->tree[u].emplace_back(v);
        edge_nodes[edge_no] = std::make_pair(u, v);
        nodes_edge[make_pair(u, v)] = edge_no;
    }
};

// uからvへいくルートを取得 O(n)
std::vector<int> get_route(const int u, const int v, const Tree &tree) {

    // get v -> u path
    std::vector<int> prev(tree.num_node, -1);
    std::stack<int> nodes;
    nodes.push(v);
    while (not nodes.empty()) {
        const auto node = nodes.top(); nodes.pop();
        if (node == u) {
            break;
        }

        for (const auto x : tree.tree[node]) {
            if (prev[x] == -1) {
                prev[x] = node;
                nodes.push(x);
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

struct TreeMovingDiv2 {
    int n;
    vector<int> roots;
    vector<int> a;
    vector<int> b;
    vector<int> c;

    int count(int _n, vector<int> _roots, vector<int> _a, vector<int> _b, vector<int> _c) {
        n = _n, roots = _roots, a = _a, b = _b, c = _c;

        int M = LEN(roots);
        auto tree_list = make_v<Tree>(M);
        FOR(i, 0, M) {
            auto X = make_v<LL>(n);
            X[0] = c[i];
            FOR(k, 1, n - 1) {
                X[k] = (a[i] * X[k - 1] + b[i]) % 1000000007;
            }

            tree_list[i].init(n);
            FOR(j, 0, n - 1) {
                LL u = (roots[i] + j + 1) % n;
                LL v = (roots[i] + (X[j] % (j + 1))) % n;
                tree_list[i].add_undirected_edge(u, v, j);
            }
        }

        mint<MOD> ans;
        FOR(first_remove, 0, n - 1) {
            auto dp = make_v<mint<MOD>>(M + 1, n);
            dp[1][first_remove] = 1;

            FOR(i, 1, M) {
                FOR(add_edge, 0, n - 1) {
                    int u, v;
                    tie(u, v) = tree_list[i - 1].edge_nodes[add_edge];

                    auto route = get_route(u, v, tree_list[i]);
                    FOR(j, 0, LEN(route) - 1) {
                        int remove_edge = tree_list[i].nodes_edge[make_pair(route[j], route[j + 1])];
                        dp[i + 1][remove_edge] += dp[i][add_edge];
                    }
                }
            }

            FOR(i, 0, n - 1) {
                int u, v;
                tie(u, v) = tree_list.back().edge_nodes[i];

                UnionFind uf(n);
                bool ok = true;
                uf.union_set(u, v);
                FOR(j, 0, n - 1) {
                    if (j == first_remove) {
                        continue;
                    }
                    int a, b;
                    tie(a, b) = tree_list[0].edge_nodes[j];
                    if (uf.is_same_set(a, b)) {
                        ok = false;
                        break;
                    }
                    uf.union_set(a, b);
                }

                if (ok) {
                    ans += dp[M][i];
                }
            }
        }

        return ans.x;
    }
};

// CUT begin
ifstream data("../SRM 711_DIV2_1000.sample");

string next_line() {
    string s;
    getline(::data, s);
    return s;
}

template<typename T>
void from_stream(T &t) {
    stringstream ss(next_line());
    ss >> t;
}

void from_stream(string &s) {
    s = next_line();
}

template<typename T>
void from_stream(vector<T> &ts) {
    int len;
    from_stream(len);
    ts.clear();
    for (int i = 0; i < len; ++i) {
        T t;
        from_stream(t);
        ts.push_back(t);
    }
}

template<typename T>
string to_string(T t) {
    stringstream s;
    s << t;
    return s.str();
}

string to_string(string t) {
    return "\"" + t + "\"";
}

bool do_test(int n, vector<int> roots, vector<int> a, vector<int> b, vector<int> c, int __expected) {
    time_t startClock = clock();
    TreeMovingDiv2 *instance = new TreeMovingDiv2();
    int __result = instance->count(n, roots, a, b, c);
    double elapsed = (double) (clock() - startClock) / CLOCKS_PER_SEC;
    delete instance;

    if (__result == __expected) {
        cout << "PASSED!" << " (" << elapsed << " seconds)" << endl;
        return true;
    } else {
        cout << "FAILED!" << " (" << elapsed << " seconds)" << endl;
        cout << "           Expected: " << to_string(__expected) << endl;
        cout << "           Received: " << to_string(__result) << endl;
        return false;
    }
}

int run_test(bool mainProcess, const set<int> &case_set, const string command) {
    int cases = 0, passed = 0;
    while (true) {
        if (next_line().find("--") != 0)
            break;
        int n;
        from_stream(n);
        vector<int> roots;
        from_stream(roots);
        vector<int> a;
        from_stream(a);
        vector<int> b;
        from_stream(b);
        vector<int> c;
        from_stream(c);
        next_line();
        int __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if (do_test(n, roots, a, b, c, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1589097587;
        double PT = T / 60.0, TT = 75.0;
        cout << "Time   : " << T / 60 << " minutes " << T % 60 << " secs" << endl;
        cout << "Score  : " << 1000 * (0.3 + (0.7 * TT * TT) / (10.0 * PT * PT + TT * TT)) << " points" << endl;
    }
    return 0;
}

int main(int argc, char *argv[]) {
    cout.setf(ios::fixed, ios::floatfield);
    cout.precision(2);
    set<int> cases;
    bool mainProcess = true;
    for (int i = 1; i < argc; ++i) {
        if (string(argv[i]) == "-") {
            mainProcess = false;
        } else {
            cases.insert(atoi(argv[i]));
        }
    }
    if (mainProcess) {
        cout << "TreeMovingDiv2 (1000 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
