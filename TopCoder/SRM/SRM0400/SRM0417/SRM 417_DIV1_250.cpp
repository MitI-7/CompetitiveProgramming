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

#define LEN(x) int(x.size())
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

// 部分文字列のhash値を計算
// https://qiita.com/keymoon/items/11fac5627672a6d6a9f6
class RollingHash {
    const uint_fast64_t  MASK30 = (1ull << 30ull) - 1;
    const uint_fast64_t  MASK31 = (1ull << 31ull) - 1;
    const uint_fast64_t  MOD = (1ull << 61ull) - 1;
    const uint_fast64_t  POSITIVIZER = MOD * ((1ull << 3ull) - 1);

    int n;
    uint_fast32_t Base;
    vector<uint_fast64_t> powMemo;
    vector<uint_fast64_t > has;

public:
    RollingHash(const std::string &s) : n(s.size()) {
        powMemo.resize(n + 1);
//        Base = (uint)new Random().Next(129, int.MaxValue);
        Base = 129;
        powMemo[0] = 1;
        for (int i = 1; i < powMemo.size(); i++) {
            powMemo[i] = calc_mod(mul(powMemo[i - 1], Base));
        }

        has.resize(s.size() + 1);
        for (int i = 0; i < s.size(); i++)
            has[i + 1] = calc_mod(mul(has[i], Base) + s[i]);
    }

    // s[left, right)のhash値 O(1)
    uint_fast64_t  hash(int left, int right) {
        assert(0 <= left and left < right and right <= n);

        const int length = right - left;
        return calc_mod(has[right] + POSITIVIZER - mul(has[left], powMemo[length]));
    }

private:
    uint_fast64_t mul(uint_fast64_t l, uint_fast64_t r) {
        uint_fast64_t lu = l >> 31ull;
        uint_fast64_t ld = l & MASK31;
        uint_fast64_t ru = r >> 31ull;
        uint_fast64_t rd = r & MASK31;
        uint_fast64_t middleBit = ld * ru + lu * rd;
        return ((lu * ru) << 1ull) + ld * rd + ((middleBit & MASK30) << 31ull) + (middleBit >> 30ull);
    }

    uint_fast64_t calc_mod(uint_fast64_t val) {
        val = (val & MOD) + (val >> 61ull);
        if (val > MOD) {
            val -= MOD;
        }
        return val;
    }
};

struct TemplateMatching {
    string text;
    string prefix;
    string suffix;
    string bestMatch(string _text, string _prefix, string _suffix) {
        text = _text, prefix = _prefix, suffix = _suffix;

        RollingHash rh_t(text);
        RollingHash rh_p(prefix);
        RollingHash rh_s(suffix);

        int best_score = -1;
        int best_pre_score = -1;
        string ans;

        FOR(b, 0, LEN(text)) {
            FOR(e, b + 1, LEN(text) + 1) {
                int len = e - b;
                int pre_score = 0, suf_score = 0;
                FOR(i, 1, min(LEN(prefix), len) + 1) {
                    if (rh_t.hash(b, b + i) == rh_p.hash(LEN(prefix) - i, LEN(prefix))) {
                        pre_score = i;
                    }
                }
                FOR(i, 1, min(LEN(suffix), len) + 1) {
                    if (rh_t.hash(e - i, e) == rh_s.hash(0, i)) {
                        suf_score = i;
                    }
                }

                if (pre_score + suf_score > best_score) {
                    best_score = pre_score + suf_score;
                    best_pre_score = pre_score;
                    ans = text.substr(b, len);
                }
                else if (pre_score + suf_score == best_score) {
                    if (pre_score > best_pre_score) {
                        best_score = pre_score + suf_score;
                        best_pre_score = pre_score;
                        ans = text.substr(b, len);
                    }
                    else if (pre_score == best_pre_score) {
                        if (ans > text.substr(b, len)) {
                            best_score = pre_score + suf_score;
                            best_pre_score = pre_score;
                            ans = text.substr(b, len);
                        }
                    }
                }
            }
        }

        return ans;
    }
};

// CUT begin
ifstream data("../SRM 417_DIV1_250.sample");

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

template <typename T>
string to_string(T t) {
    stringstream s;
    s << t;
    return s.str();
}

string to_string(string t) {
    return "\"" + t + "\"";
}

bool do_test(string text, string prefix, string suffix, string __expected) {
    time_t startClock = clock();
    TemplateMatching *instance = new TemplateMatching();
    string __result = instance->bestMatch(text, prefix, suffix);
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
        string text;
        from_stream(text);
        string prefix;
        from_stream(prefix);
        string suffix;
        from_stream(suffix);
        next_line();
        string __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if ( do_test(text, prefix, suffix, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1585465709;
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
        if ( string(argv[i]) == "-") {
            mainProcess = false;
        } else {
            cases.insert(atoi(argv[i]));
        }
    }
    if (mainProcess) {
        cout << "TemplateMatching (250 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
