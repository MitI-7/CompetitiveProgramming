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

// 最大流問題を解く O(|E||V|^2)
class Dinic {

public:
    struct Edge {
        const int to;         // 行き先のノードid
        long long flow;       // 流量
        const long long cap;  // 容量
        const int rev;        // 逆辺のノードid
        const bool is_rev;    // 逆辺かどうか
        Edge(int to, long long flow, long long cap, int rev, bool is_rev) : to(to), flow(flow), cap(cap), rev(rev), is_rev(is_rev) {
            assert(this->cap >= 0);
        }
    };

    vector<vector<Edge>> graph; // グラフの隣接リスト表現
    vector<int> level;          // sからの距離
    vector<unsigned int> iter;  // どこまで調べ終わったか

    explicit Dinic(unsigned int num_of_node) {
        assert(num_of_node > 0);
        graph.resize(num_of_node);
        level.resize(num_of_node);
        iter.resize(num_of_node);
    }

    // fromからtoへ向かう容量capの辺をグラフに追加する
    void add_edge(unsigned int from, unsigned int to, long long cap) {
        graph[from].emplace_back(Edge(to, 0, cap, (unsigned int)graph[to].size(), false));
        graph[to].emplace_back(Edge(from, cap, cap, (unsigned int)graph[from].size() - 1, true));
    }

    // sからtへの最大流を求める
    long long max_flow(unsigned int s, unsigned int t) {
        long long flow = 0;
        while (true) {
            bfs(s);
            if (level.at(t) < 0) {
                return flow;
            }
            fill(iter.begin(), iter.end(), 0);
            long long f;
            while ((f = dfs(s, t, INT_MAX)) > 0) {
                flow += f;
            }
        }
    }

private:
    // sからの最短距離をBFSで計算する
    void bfs(unsigned int s) {
        fill(level.begin(), level.end(), -1);
        queue<unsigned int> que;
        level.at(s) = 0;
        que.push(s);
        while (not que.empty()) {
            unsigned int v = que.front();
            que.pop();
            for (int i = 0; i < graph.at(v).size(); ++i) {
                Edge &e = graph.at(v).at(i);
                if ((e.cap - e.flow) > 0 and level.at(e.to) < 0) {
                    level.at(e.to) = level.at(v) + 1;
                    que.push(e.to);
                }
            }
        }
    }

    // 増加パスをDFSで探す
    long long dfs(unsigned int v, unsigned int t, long long f) {
        if (v == t) {
            return f;
        }
        for (unsigned int &i = iter.at(v); i < graph.at(v).size(); ++i) {
            Edge &e = graph.at(v).at(i);
            if ((e.cap - e.flow) > 0 and level.at(v) < level.at(e.to)) {
                long long d = dfs(e.to, t, min(f, e.cap - e.flow));
                if (d > 0) {
                    e.flow += d;
                    graph.at(e.to).at(e.rev).flow -= d;
                    return d;
                }
            }
        }
        return 0;
    }
};

struct BlockTheBlockPuzzle {
    vector<string> board;

    int calc_cost(pair<int, int> p1, pair<int, int> p2) {
        int y1 = p1.first;
        int x1 = p1.second;
        int y2 = p2.first;
        int x2 = p2.second;

        char a, b;
        if (y1 == y2 and abs(x1 - x2) == 3) {
            int x = min(x1, x2);
            a = board[y1][x + 1];
            b = board[y1][x + 2];
        }
        else if (x1 == x2 and abs(y1 - y2) == 3) {
            int y = min(y1, y2);
            a = board[y + 1][x1];
            b = board[y + 2][x1];
        }
        else {
            return -1;
        }

        if (a == 'b' or b == 'b') {
            return INF;
        }
        if (a == '.' and b == '.') {
            return 2;
        }
        if (a == 'H' and b == 'H') {
            return 0;
        }
        return 1;
    }

    int minimumHoles(vector<string> _board) {
        board = _board;

        int H = LEN(board);
        int W = LEN(board[0]);

        int gy = -1, gx = -1;
        FOR(y, 0, H) {
            FOR(x, 0, W) {
                if (board[y][x] == '$') {
                    gy = y;
                    gx = x;
                }
            }
        }

        auto start = make_v<pair<int, int>>(0);
        auto nodes = make_v<pair<int, int>>(0);
        FOR(y, 0, H) {
            FOR(x, 0, W) {
                if ((gy - y) % 3 == 0 and (gx - x) % 3 == 0) {
                    if (board[y][x] == 'b') {
                        start.emplace_back(make_pair(y, x));
                    }
                    else if (board[y][x] == '.') {
                        nodes.emplace_back(make_pair(y, x));
                    }
                }
            }
        }

        int num_of_nodes = LEN(start) + LEN(nodes) * 2 + 1 + 1;
        int source = num_of_nodes - 2;
        int goal = num_of_nodes - 1;

        Dinic dinic(num_of_nodes);

        // source -> start
        FOR(i, 0, LEN(start)) {
            dinic.add_edge(source, i, INF);
        }

        // start -> node_1
        FOR(i, 0, LEN(start)) {
            FOR(j, 0, LEN(nodes)) {
                int c = calc_cost(start[i], nodes[j]);
                if (c != -1) {
                    dinic.add_edge(i, LEN(start) + j * 2, c);
                }
            }
        }

        // node -> node
        FOR(i, 0, LEN(nodes)) {
            FOR(j, 0, LEN(nodes)) {
                if (i == j) {
                    // same node
                    dinic.add_edge(LEN(start) + i * 2, LEN(start) + i * 2 + 1, 1);
                }
                else {
                    int c = calc_cost(nodes[i], nodes[j]);
                    if (c != -1) {
                        dinic.add_edge(LEN(start) + i * 2 + 1, LEN(start) + j * 2, c);
                    }
                }
            }
        }

        // start -> goal
        FOR(i, 0, LEN(start)) {
            int c = calc_cost(start[i], make_pair(gy, gx));
            if (c != -1) {
                dinic.add_edge(i, goal, c);
            }
        }

        // node_2 -> goal
        FOR(i, 0, LEN(nodes)) {
            int c = calc_cost(nodes[i], make_pair(gy, gx));
            if (c != -1) {
                dinic.add_edge(LEN(start) + i * 2 + 1, goal, c);
            }
        }

        LL mf = dinic.max_flow(source, goal);
        if (mf >= INF) {
            return -1;
        }

        return mf;
    }
};

// CUT begin
ifstream data("../SRM 625_DIV1_500.sample");

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

bool do_test(vector<string> board, int __expected) {
    time_t startClock = clock();
    BlockTheBlockPuzzle *instance = new BlockTheBlockPuzzle();
    int __result = instance->minimumHoles(board);
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
        vector<string> board;
        from_stream(board);
        next_line();
        int __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if ( do_test(board, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1590560443;
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
        cout << "BlockTheBlockPuzzle (500 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
