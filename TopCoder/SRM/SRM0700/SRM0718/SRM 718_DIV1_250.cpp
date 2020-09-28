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

static const int MOD = 1000000000 + 7;

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

template<typename T>class CumulativeSum {
public:
    std::vector<T> memo1;               // 1次元用の累積和表
    std::vector<std::vector<T>> memo2;  // 2次元用の累積和表

    CumulativeSum() {}

    void build(const std::vector<T> &line) {
        this->memo1.assign(line.size() + 1, 0);

        for (int i = 0; i < line.size(); ++i) {
            this->memo1[i + 1] = this->memo1[i] + line[i];
        }
    }

    // 2次元の累積和表を作成
    void build(const std::vector<std::vector<T>> &board) {
        int height = board.size();
        int width = board[0].size();
        this->memo2.assign(height + 1, std::vector<T>(width + 1, 0));

        for (int y = 0; y < height; ++y) {
            for (int x = 0; x < width; ++x) {
                memo2[y + 1][x + 1] = board[y][x] + memo2[y + 1][x];
            }
            for (int x = 0; x < width; ++x) {
                memo2[y + 1][x + 1] += memo2[y][x + 1];
            }
        }
    }

    T sum(int left, int right) {
        return this->memo1[right] - this->memo1[left];
    }

    /*
    (y1, x1)から(y2, x2)の合計を返す．(y2, x2)は含まない
    座標はmemoを作成したboard準拠
    (ex, sum(0, 0, 2, 2)なら(0, 0), (0, 1), (1, 0), (1, 1)の合計を返す)
    */
    T sum(int y1, int x1, int y2, int x2) {
        return this->memo2[y2][x2] - this->memo2[y2][x1] - this->memo2[y1][x2] + this->memo2[y1][x1];
    }
};

struct InterleavingParenthesis {
    string s1;
    string s2;
    int countWays(string _s1, string _s2) {
        s1 = _s1, s2 = _s2;
        auto N = LEN(s1);
        auto M = LEN(s2);

        auto b1 = make_v<int>(N);
        auto b2 = make_v<int>(M);
        FOR(i, 0, N) {
            b1[i] = (s1[i] == '(');
        }
        FOR(i, 0, M) {
            b2[i] = (s2[i] == '(');
        }

        CumulativeSum<int> cs1; cs1.build(b1);
        CumulativeSum<int> cs2; cs2.build(b2);

        if ((cs1.sum(0, N) + cs2.sum(0, M)) * 2 != N + M) {
            return 0;
        }

        auto dp = make_v<mint<MOD>>(2600, 2600);
        dp[0][0] = 1;

        FOR(i, 0, N + 1) {
            FOR(j, 0, M + 1) {
                if (dp[i][j].x == 0) {
                    continue;
                }

                int left = cs1.sum(0, i) + cs2.sum(0, j);

                // use s1
                if (i < N) {
                    if (b1[i] == 1) {
                        dp[i + 1][j] += dp[i][j];
                    } else {
                        if (left * 2 > i + j) {
                            dp[i + 1][j] += dp[i][j];
                        }
                    }
                }

                // use s2
                if (j < M) {
                    if (b2[j] == 1) {
                        dp[i][j + 1] += dp[i][j];
                    } else {
                        if (left * 2 > i + j) {
                            dp[i][j + 1] += dp[i][j];
                        }
                    }
                }
            }
        }

        return dp[N][M].x;
    }
};

// CUT begin
ifstream data("../SRM 718_DIV1_250.sample");

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

bool do_test(string s1, string s2, int __expected) {
    time_t startClock = clock();
    InterleavingParenthesis *instance = new InterleavingParenthesis();
    int __result = instance->countWays(s1, s2);
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
        string s1;
        from_stream(s1);
        string s2;
        from_stream(s2);
        next_line();
        int __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if ( do_test(s1, s2, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1591584420;
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
        cout << "InterleavingParenthesis (250 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
