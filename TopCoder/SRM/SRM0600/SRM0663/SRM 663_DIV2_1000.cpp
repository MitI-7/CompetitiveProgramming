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

template <typename T> bool next_combination(const T first, const T last, int k) {
    const T subset = first + k;
    // empty container | k = 0 | k == n
    if (first == last || first == subset || last == subset) {
        return false;
    }
    T src = subset;
    while (first != src) {
        src--;
        if (*src < *(last - 1)) {
            T dest = subset;
            while (*src >= *dest) {
                dest++;
            }
            iter_swap(src, dest);
            rotate(src + 1, dest + 1, last);
            rotate(subset, subset + (last - dest) - 1, last);
            return true;
        }
    }
    // restore
    rotate(first, subset, last);
    return false;
}

struct CheeseRolling {
    vector<vector<int>> wins;

    int win(const vector<int> &member) {
        deque<int> deq;
        FOE(m, member) {
            deq.emplace_back(m);
        }
        while (LEN(deq) != 1) {
            int a = deq.front(); deq.pop_front();
            int b = deq.front(); deq.pop_front();
            if (wins[a][b]) {
                deq.emplace_back(a);
            }
            else {
                deq.emplace_back(b);
            }
        }

        return deq.front();
    }

    vector<LL> solve(vector<int> &member) {
        vector<LL> ans(16);
        sort(ALL(member));
        do {
            ans[win(member)]++;
        } while (next_permutation(ALL(member)));

        return ans;
    }

    vector<LL> solve2(vector<int> &member, map<unsigned int, vector<LL>> &memo2) {
        assert(LEN(member) == 8);
        vector<LL> ans(16);

        unsigned int mask = 0;
        FOE(m, member) {
            mask = bit_set(mask, m, 1);
        }

        sort(ALL(member));
        do {
            unsigned int bit = 0;
            FOR(i, 0, 4) {
                bit = bit_set(bit, member[i], 1);
            }

            auto a = memo2[bit];
            auto b = memo2[bit ^ mask];

            if (a.empty() or b.empty()) {
                continue;
            }
            FOR(i, 0, 16) {
                FOR(j, 0, 16) {
                    if (wins[i][j]) {
                        ans[i] += a[i] * b[j];
                    }
                    else {
                        ans[j] += a[i] * b[j];
                    }
                }
            }
        } while (next_combination(ALL(member), 4));

        return ans;
    }

    vector<long long> waysToWin(vector<string> _wins) {
        int N = LEN(_wins);
        wins = make_v<int>(N, N);
        FOR(i, 0, N) {
            FOR(j, 0, N) {
                wins[i][j] = _wins[i][j] == 'Y';
            }
        }

        vector<LL> ans(N);
        vector<int> member(N);
        iota(ALL(member), 0);

        if (N <= 8) {
            auto m = solve(member);
            FOR(i, 0, N) {
                ans[i] = m[i];
            }
        } else {
            map<unsigned int, vector<LL>> memo4;
            do {
                unsigned int used = 0;
                vector<int> v;
                FOR(i, 0, 4) {
                    used = bit_set(used, member[i], 1);
                    v.emplace_back(member[i]);
                }
                memo4[used] = solve(v);
            } while (next_combination(ALL(member), 4));

            sort(ALL(member));
            map<unsigned int, vector<LL>> memo8;
            do {
                unsigned int used = 0;
                vector<int> v;
                FOR(i, 0, 8) {
                    used = bit_set(used, member[i], 1);
                    v.emplace_back(member[i]);
                }
                memo8[used] = solve2(v, memo4);
            } while (next_combination(ALL(member), 8));

            FOE(p, memo8) {
                auto a = p.second;
                auto b = memo8[p.first ^ 0b1111111111111111];

                FOR(i, 0, 16) {
                    FOR(j, 0, 16) {
                        if (wins[i][j]) {
                            ans[i] += a[i] * b[j];
                        }
                        else {
                            ans[j] += a[i] * b[j];
                        }
                    }
                }
            }
        }

        return ans;
    }
};

// CUT begin
ifstream data("../SRM 663_DIV2_1000.sample");

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

template<typename T>
string to_string(vector<T> ts) {
    stringstream s;
    s << "[ ";
    for (int i = 0; i < ts.size(); ++i) {
        if (i > 0) s << ", ";
        s << to_string(ts[i]);
    }
    s << " ]";
    return s.str();
}

bool do_test(vector<string> wins, vector<long long> __expected) {
    time_t startClock = clock();
    CheeseRolling *instance = new CheeseRolling();
    vector<long long> __result = instance->waysToWin(wins);
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
        vector<string> wins;
        from_stream(wins);
        next_line();
        vector<long long> __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if (do_test(wins, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1588482383;
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
        cout << "CheeseRolling (1000 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
