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

long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}

long long sum_of_geometric_progressions(long long a, long long r, long long n) {
    return a * (1 - (long long)pow(r, n)) / (1 - r);
}

long long sum_of_geometric_progressions_mod(long long a, long long r, long long n, long long mod) {
    if (n == 1) {
        return a % mod;
    }

    long long x = sum_of_geometric_progressions_mod(a, r, n/2, mod);
    long long ret = (x + powmod(r, n/2, mod) * x) % mod;
    if (n & 1) {
        ret = (a + r * ret) % mod;
    }
    return ret;
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

static const int MOD = 1000000000 + 7;

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

class Tree {
public:
    int num_of_node;
    std::vector<std::vector<int>> tree;
    std::vector<int> parent;
    std::vector<vector<int>> children;

    Tree() {}

    Tree(int num_of_node) {
        init(num_of_node);
    }

    void init(int _num_of_node) {
        this->num_of_node = _num_of_node;
        this->tree.resize(_num_of_node);
        this->parent.resize(_num_of_node);
        this->children.resize(_num_of_node);
    }

    // u <-> v
    void add_undirected_edge(int u, int v) {
        this->tree[u].emplace_back(v);
        this->tree[v].emplace_back(u);
    }

    // u -> v
    void add_directed_edge(int u, int v) {
        this->parent[v] = u;
        this->children[u].emplace_back(v);
    }

    // 無向木を有向木にする
    void build_directed_tree(const int root) {
        this->dfs(root, -1);
    }

private:
    void dfs(const int u, const int p) {
        this->parent[u] = p;
        for (int v : this->tree[u]) {
            if (v != p) {
                this->children[u].emplace_back(v);
                dfs(v, u);
            }
        }
    }
};

// call depth_dfs(root, 0, depth, tree)
void depth_dfs(int u, long long d, vector<long long> &depth, Tree &tree) {
    depth[u] = d;
    for (auto v : tree.children[u]) {
        depth_dfs(v, d + 1, depth, tree);
    }
}

LL counter = 1;
LL T_dfs(int u, vector<LL> &T, vector<LL> &max_T, Tree &tree) {
    T[u] = counter++;
    max_T[u] = T[u];
    for (auto v : tree.children[u]) {
        chmax(max_T[u], T_dfs(v, T, max_T, tree));
    }
    return max_T[u];
}

struct ETSums {
    int N;
    vector<int> parent;
    vector<int> cost;
    int D;
    int seed;
    int MX;

    int findSumOfETSums(int _N, vector<int> _parent, vector<int> _cost, int _D, int _seed, int _MX) {
        N = _N, parent = _parent, cost = _cost, D = _D, seed = _seed, MX = _MX;

        auto A = make_v<LL>(2 * N);
        auto P = make_v<LL>(N);
        auto C = make_v<LL>(N);
        A[0] = seed;
        FOR(i, 1, 2 * N) {
            A[i] = (A[i - 1] * 1103515245 + 12345) % 2147483648;
        }

        FOR(i, 0, N) {
            if (i < LEN(parent)) {
                P[i] = parent[i];
            } else {
                P[i] = (A[i] % min(i, D)) + i - min(i, D);
            }
        }

        FOR(i, 0, N) {
            if (i < LEN(cost)) {
                C[i] = cost[i];
            } else {
                C[i] = A[N + i] % MX;
            }
        }

        Tree tree(N);
        FOR(u, 1, N) {
            tree.add_directed_edge(P[u], u);
        }

        auto depth = make_v<LL>(N);
        auto T = make_v<LL>(N);
        auto max_T = make_v<LL>(N);

        depth_dfs(0, 0, depth, tree);
        counter = 1;
        T_dfs(0, T, max_T, tree);

        mint<MOD> ans = 0;
        FOR(u, 0, N) {
            LL num = max_T[u] - T[u] + 1;
            LL a = powmod(depth[u], T[u], MOD);
            ans += C[u] * sum_of_geometric_progressions_mod(a, depth[u], num, MOD);
        }

        return ans.x;
    }
};

// CUT begin
ifstream data("../SRM 763_DIV2_1000.sample");

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

bool do_test(int N, vector<int> parent, vector<int> cost, int D, int seed, int MX, int __expected) {
    time_t startClock = clock();
    ETSums *instance = new ETSums();
    int __result = instance->findSumOfETSums(N, parent, cost, D, seed, MX);
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
        int N;
        from_stream(N);
        vector<int> parent;
        from_stream(parent);
        vector<int> cost;
        from_stream(cost);
        int D;
        from_stream(D);
        int seed;
        from_stream(seed);
        int MX;
        from_stream(MX);
        next_line();
        int __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if (do_test(N, parent, cost, D, seed, MX, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1589429515;
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
        cout << "ETSums (1000 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
