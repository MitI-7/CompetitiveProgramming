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

struct ConstructLCS {

    // sとtの最長共通部分列の長さを算出
    int longest_common_subsequence(const string &s, const string &t) {
        int ans = 0;
        vector<vector<int>> dp(s.size() + 1, vector<int>(t.size() + 1, 0));

        for (int i = 1; i < (int)dp.size(); ++i) {
            for (int j = 1; j < (int)dp[0].size(); ++j) {
                if (s[i - 1] == t[j - 1]) {
                    dp[i][j] = max(dp[i][j], dp[i - 1][j - 1] + 1);
                }
                else {
                    dp[i][j] = max(dp[i][j], max(dp[i - 1][j], dp[i][j - 1]));
                }
                ans = max(ans, dp[i][j]);
            }
        }

        return ans;
    }

    vector<string> solve(int ab, int bc, int ca) {
        vector<int> nums = {ab, bc, ca};
        sort(ALL(nums));

        string a, b, c;
        FOR(i, 0, nums[1]) {
            b += "0";
            c += "0";
        }
        FOR(i, 0, nums[0]) {
            a += "0";
        }
        FOR(i, 0, nums[2] - nums[0]) {
            a += "1";
            b += "1";
        }

        vector<string> v = {a, b, c};
        FOR(i, 0, 3) {
            FOR(j, 0, 3) {
                FOR(k, 0, 3) {
                    if (i != j and i != k and j != k) {
                        int ij = longest_common_subsequence(v[i], v[j]);
                        int jk = longest_common_subsequence(v[j], v[k]);
                        int ik = longest_common_subsequence(v[i], v[k]);
                        if (ij == ab and jk == bc and ik == ca) {
                            return {v[i], v[j], v[k]};
                        }
                    }
                }
            }
        }
        return {};
    }

    string construct(int ab, int bc, int ca) {
        auto ans = solve(ab, bc, ca);
        return ans[0] + " " + ans[1] + " " + ans[2];
    }
};

// CUT begin
ifstream data("../SRM 716_DIV1_250.sample");

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
string to_string(T t) {
    stringstream s;
    s << t;
    return s.str();
}

string to_string(string t) {
    return "\"" + t + "\"";
}

bool do_test(int ab, int bc, int ca, string __expected) {
    time_t startClock = clock();
    ConstructLCS *instance = new ConstructLCS();
    string __result = instance->construct(ab, bc, ca);
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
        int ab;
        from_stream(ab);
        int bc;
        from_stream(bc);
        int ca;
        from_stream(ca);
        next_line();
        string __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if (do_test(ab, bc, ca, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1591757175;
        double PT = T / 60.0, TT = 75.0;
        cout << "Time   : " << T / 60 << " minutes " << T % 60 << " secs" << endl;
        cout << "Score  : " << 250 * (0.3 + (0.7 * TT * TT) / (10.0 * PT * PT + TT * TT)) << " points" << endl;
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
        cout << "ConstructLCS (250 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
