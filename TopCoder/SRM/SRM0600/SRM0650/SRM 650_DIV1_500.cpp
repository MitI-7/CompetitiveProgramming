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

using namespace std;

void dfs(int u, vector<bool> &used, pair<int, int> ng, vector<vector<int>> &graph) {
    used[u] = true;
    FOE(v, graph[u]) {
        if (not used[v]) {
            if (u == ng.first and v == ng.second) {
                continue;
            }
            if (v == ng.first and u == ng.second) {
                continue;
            }

            dfs(v, used, ng, graph);
        }
    }
}

class Tree {
public:
    int num_of_node;
    std::vector<std::vector<int>> tree;
    std::vector<int> parent;
    std::vector<vector<int>> children;

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

    void clear() {
//        this->tree.clear();
//        this->tree.resize(num_of_node);
        this->parent.clear();
        this->parent.resize(num_of_node, -1);
        this->children.clear();
        this->children.resize(num_of_node);
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

    // 無向木を有向木にする
    bool build_directed_tree(const int root) {
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

bool is_complete_binary_tree(Tree &tree) {
    int root = -1;
    std::vector<int> nodes;
    for (int u = 0; u < tree.num_of_node; ++u) {
        // leaf
        if (tree.tree[u].size() == 1) {
            nodes.emplace_back(u);
        }
        else if (tree.tree[u].size() == 2) {
            if (root != -1) {
                return false;
            }
            root = u;
        }
        else if (tree.tree[u].size() > 3) {
            return false;
        }
    }

    if (root == -1) {
        return false;
    }

    bool ok = tree.build_directed_tree(root);
    // not tree
    if (not ok) {
        return false;
    }

    vector<int> count(tree.num_of_node);
    while (nodes.size() > 1) {
        std::vector<int> next_nodes;

        for (auto u : nodes) {
            auto p = tree.parent[u];
            if (p == -1) {
                return false;
            }

            if (count[p] == 0) {
                next_nodes.emplace_back(p);
            }
            count[p]++;

            if (count[p] > 2) {
                return false;
            }
        }

        if (next_nodes.size() * 2 != nodes.size()) {
            return false;
        }
        nodes = next_nodes;
    }

    return nodes.size() == 1 and nodes[0] == root;
}

struct TheKingsRoadsDiv1 {
    int h;
    vector<int> a;
    vector<int> b;
    string getAnswer(int _h, vector<int> _a, vector<int> _b) {
        h = _h, a = _a, b = _b;

        FOR(i, 0, LEN(a)) {
            a[i]--;
            b[i]--;
        }

        int N = pow(2, h) - 1;
        auto graph = make_v<int>(N, 0);
        auto loop = make_v<int>(0);
        int num_must = 0;
        auto must = make_v<bool>(LEN(a));
        set<pair<int, int>> s;
        FOR(i, 0, LEN(a)) {

            // self
            if (a[i] == b[i]) {
                num_must++;
                must[i] = true;
                continue;
            }
            // multi
            if (s.find(make_pair(min(a[i], b[i]), max(a[i], b[i]))) != s.end()) {
                num_must++;
                must[i] = true;
                continue;
            }

            graph[a[i]].emplace_back(b[i]);
            graph[b[i]].emplace_back(a[i]);
            s.emplace(make_pair(min(a[i], b[i]), max(a[i], b[i])));
        }


        FOR(i, 0, LEN(a)) {
            if (must[i]) {
                loop.emplace_back(i);
                continue;
            }
            auto used = make_v<bool>(N);
            dfs(a[i], used, make_pair(a[i], b[i]), graph);

            if (used[b[i]]) {
                loop.emplace_back(i);
            }
        }
        sort(ALL(loop));

        if (loop.size() >= 65) {
            return "Incorrect";
        }

        Tree tree(N);
        FOR(i, 0, LEN(a)) {
            if (not must[i]) {
                tree.add_undirected_edge(a[i], b[i]);
            }
        }

        FOR(i, 0, LEN(loop)) {
            if (not must[loop[i]]) {
                tree.remove_undirected_edge(a[loop[i]], b[loop[i]]);
            }

            FOR(j, i + 1, LEN(loop)) {
                if (not must[loop[j]]) {
                    tree.remove_undirected_edge(a[loop[j]], b[loop[j]]);
                }

                FOR(k, j + 1, LEN(loop)) {

                    if (int(must[loop[i]]) + int(must[loop[j]]) + int(must[loop[k]]) != num_must) {
                        continue;
                    }

                    tree.clear();

                    if (not must[loop[k]]) {
                        tree.remove_undirected_edge(a[loop[k]], b[loop[k]]);
                    }

                    if (is_complete_binary_tree(tree)) {
                        return "Correct";
                    }

                    if (not must[loop[k]]) {
                        tree.add_undirected_edge(a[loop[k]], b[loop[k]]);
                    }
                }
                if (not must[loop[j]]) {
                    tree.add_undirected_edge(a[loop[j]], b[loop[j]]);
                }
            }
            if (not must[loop[i]]) {
                tree.add_undirected_edge(a[loop[i]], b[loop[i]]);
            }
        }

        return "Incorrect";
    }
};

// CUT begin
ifstream data("../SRM 650_DIV1_500.sample");

string next_line() {
    string s;
    getline(::data, s);
    return s;
}

template <typename T> void from_stream(T &t) {
    stringstream ss(next_line());
    ss >> t;
}

void from_stream(string &s) {
    s = next_line();
}

template <typename T> void from_stream(vector<T> &ts) {
    int len;
    from_stream(len);
    ts.clear();
    for (int i = 0; i < len; ++i) {
        T t;
        from_stream(t);
        ts.push_back(t);
    }
}

template <typename T>
string to_string(T t) {
    stringstream s;
    s << t;
    return s.str();
}

string to_string(string t) {
    return "\"" + t + "\"";
}

bool do_test(int h, vector<int> a, vector<int> b, string __expected) {
    time_t startClock = clock();
    TheKingsRoadsDiv1 *instance = new TheKingsRoadsDiv1();
    string __result = instance->getAnswer(h, a, b);
    double elapsed = (double)(clock() - startClock) / CLOCKS_PER_SEC;
    delete instance;

    if (__result == __expected) {
        cout << "PASSED!" << " (" << elapsed << " seconds)" << endl;
        return true;
    }
    else {
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
        int h;
        from_stream(h);
        vector<int> a;
        from_stream(a);
        vector<int> b;
        from_stream(b);
        next_line();
        string __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if ( do_test(h, a, b, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1590216873;
        double PT = T / 60.0, TT = 75.0;
        cout << "Time   : " << T / 60 << " minutes " << T % 60 << " secs" << endl;
        cout << "Score  : " << 500 * (0.3 + (0.7 * TT * TT) / (10.0 * PT * PT + TT * TT)) << " points" << endl;
    }
    return 0;
}

int main(int argc, char *argv[]) {
    cout.setf(ios::fixed, ios::floatfield);
    cout.precision(2);
    set<int> cases;
    bool mainProcess = true;
    for (int i = 1; i < argc; ++i) {
        if ( string(argv[i]) == "-") {
            mainProcess = false;
        } else {
            cases.insert(atoi(argv[i]));
        }
    }
    if (mainProcess) {
        cout << "TheKingsRoadsDiv1 (500 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
