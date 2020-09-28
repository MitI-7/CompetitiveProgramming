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

// 強連結成分分解(一意に定まりDAGになる)
class StronglyConnectedComponents {
public:
    int num_component = -1;
    std::vector<int> node_component;                       // 元のノード番号 -> コンポーネントのノード番号
    std::vector<std::unordered_set<int>> component_node;   // コンポーネントのノード番号 -> 元のノード番号

private:
    const int N;
    std::vector<std::vector<int>> graph;
    std::vector<std::vector<int>> rev_graph;

public:
    // N: 頂点数
    StronglyConnectedComponents(int N) : N(N) {
        this->graph.resize(N);
        this->rev_graph.resize(N);
        this->node_component.resize(N);
    }

    void add_directed_edge(const int from, const int to) {
        this->graph[from].push_back(to);
        this->rev_graph[to].push_back(from);
    }

    // O(|V| + |E|)
    // コンポーネント数を返す
    int build() {
        std::vector<int> vs; // 帰りがけ順の並び
        {
            std::vector<bool> used(this->N);
            for (int u = 0; u < this->N; ++u) {
                if (not used[u]) {
                    this->dfs(u, used, vs);
                }
            }
        }

        std::vector<bool> used(N);
        this->num_component = 0;
        for (int i = int(vs.size()) - 1; i >= 0; --i) {
            if (not used[vs[i]]) {
                this->rdfs(vs[i], this->num_component++, used);
            }
        }

        return this->num_component;
    }

    // 強連結成分をひとつのノードにまとめたグラフを返す
    std::vector<std::vector<int>> make_new_graph() {
        this->component_node.resize(this->num_component);
        std::vector<std::vector<int>> new_graph(this->num_component);
        std::set<std::pair<int, int>> used;

        FOR(u, 0, N) {
            FOE(v, graph[u]) {
                const int new_u = this->node_component[u];
                const int new_v = this->node_component[v];

                this->component_node[new_u].insert(u);
                this->component_node[new_v].insert(v);
                if (new_u == new_v) {
                    continue;
                }
                if (used.find(std::make_pair(new_u, new_v)) == used.end()) {
                    new_graph[new_u].emplace_back(new_v);
                    used.insert(std::make_pair(new_u, new_v));
                }
            }
        }

        return new_graph;
    }

private:
    void dfs(int u, std::vector<bool> &used, std::vector<int> &vs) {
        used[u] = true;
        for (int i = 0; i < graph[u].size(); i++) {
            if (not used[graph[u][i]]) {
                dfs(graph[u][i], used, vs);
            }
        }
        vs.emplace_back(u);
    }

    void rdfs(int v, int k, std::vector<bool> &used) {
        used[v] = true;
        this->node_component[v] = k;
        for (int i = 0; i < rev_graph[v].size(); i++) {
            if (not used[rev_graph[v][i]]) {
                this->rdfs(rev_graph[v][i], k, used);
            }
        }
    }
};

class TopologicalSort {
    const int N;                           // ノード数
    std::vector<std::vector<int>> graph;   // グラフ
    std::vector<bool> used;                // 使用済みノード
    std::vector<int> indeg;                // 入次数

public:
    std::vector<int> result; // ソート結果

public:
    TopologicalSort(unsigned int num_node) : N(num_node) {
        this->graph.resize(num_node);
        this->indeg.resize(num_node, 0);
        this->used.resize(num_node, false);
    }

    // u -> vのedgeを追加
    void add(int u, int v) {
        assert(u != v);
        this->graph[u].emplace_back(v);
    }

    // O(V + E)
    bool sort() {
        // すべてのノードの入次数を算出
        for (int u = 0; u < this->N; ++u) {
            for (int v : this->graph[u]) {
                this->indeg[v]++;
            }
        }


        for (int u = 0; u < this->N; ++u) {
            if (this->indeg[u] == 0 and not this->used[u]) {
                bfs(u);
            }
        }

        return (int)this->result.size() == this->N;
    }

    // グラフの有向パスのうち最長のものの長さ
    // ソート結果が一意なら返り値はN - 1になり，元のグラフはハミルトン路を含むグラフである
    int longest_distance() {
        int ans = 0;
        std::vector<int> distance(this->N, 0);
        for (int u : this->result) {
            for (int v : this->graph[u]) {
                distance[v] = max(distance[v], distance[u] + 1);
                ans = max(ans, distance[v]);
            }
        }

        return ans;
    }

private:
    void bfs(const int s) {
        std::queue<int> que;
        que.push(s);
        this->used[s] = true;
        while (not que.empty()) {
            const int u = que.front();
            que.pop();
            this->result.emplace_back(u);

            for (int v : this->graph[u]) {
                this->indeg[v]--;
                if (this->indeg[v] == 0 and not this->used[v]) {
                    this->used[v] = true;
                    que.push(v);
                }
            }
        }
    }
};

struct Autohamil {
    vector<int> z0;
    vector<int> z1;
    string check(vector<int> _z0, vector<int> _z1) {
        z0 = _z0, z1 = _z1;

        int N = LEN(z0);
        StronglyConnectedComponents scc(N);
        FOR(i, 0, N) {
            scc.add_directed_edge(i, z0[i]);
            if (z0[i] != z1[i]) {
                scc.add_directed_edge(i, z1[i]);
            }
        }
        scc.build();
        auto graph = scc.make_new_graph();
        const int start = scc.node_component[0];

        TopologicalSort ts(LEN(graph));
        FOR(u, 0, LEN(graph)) {
            FOE(v, graph[u]) {
                ts.add(u, v);
            }
        }
        ts.sort();

        if (ts.longest_distance() == LEN(graph) - 1) {
            if (ts.result[0] == start) {
                return "Exists";
            }
        }

        return "Does not exist";
    }
};

// CUT begin
ifstream data("../SRM 684_DIV2_900.sample");

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

bool do_test(vector<int> z0, vector<int> z1, string __expected) {
    time_t startClock = clock();
    Autohamil *instance = new Autohamil();
    string __result = instance->check(z0, z1);
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
        vector<int> z0;
        from_stream(z0);
        vector<int> z1;
        from_stream(z1);
        next_line();
        string __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if ( do_test(z0, z1, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1592889573;
        double PT = T / 60.0, TT = 75.0;
        cout << "Time   : " << T / 60 << " minutes " << T % 60 << " secs" << endl;
        cout << "Score  : " << 900 * (0.3 + (0.7 * TT * TT) / (10.0 * PT * PT + TT * TT)) << " points" << endl;
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
        cout << "Autohamil (900 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
