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

class Matrix {
public:
    int m;
    int n;
    std::vector<std::vector<long long>> matrix;

    Matrix(std::vector<std::vector<long long>> matrix) : matrix(matrix) {
        this->m = matrix.size();
        this->n = matrix[0].size();
    }

    // m行n列の行列
    Matrix(int m, int n) : m(m), n(n) {
        matrix.resize(m, vector<long long>(n));
    }

    // m行m列の単位行列を生成
    static Matrix identity_matrix(int m) {
        auto a = Matrix(m, m);
        for (int i = 0; i < m; ++i) {
            a.matrix[i][i] = 1;
        }
        return a;
    }

    void multiple(const Matrix &a, const long long mod = 0LL) {
        assert(this->n == a.m);
        Matrix b = Matrix::matrix_multiple(*this, a, mod);
        this->m = b.m;
        this->n = b.n;
        this->matrix = b.matrix;
    }

    static Matrix matrix_multiple(const Matrix &a, const Matrix &b, const long long mod = 0LL) {
        assert(a.n == b.m);
        Matrix c(a.m, b.n);
        for (int i = 0; i < a.m; ++i) {
            for (int k = 0; k < a.n; ++k) {
                for (int j = 0; j < b.n; ++j) {
                    if (mod == 0) {
                        c.matrix[i][j] = c.matrix[i][j] + a.matrix[i][k] * b.matrix[k][j];
                    }
                    else {
                        c.matrix[i][j] = c.matrix[i][j] + a.matrix[i][k] * b.matrix[k][j];
                        c.matrix[i][j] %= mod;
                    }
                }
            }
        }

        return c;
    }

    void pow(const long long k, const long long mod = 0LL) {
        assert(this->m == this->n);
        auto a = Matrix::matrix_pow(*this, k, mod);
        this->m = a.m;
        this->n = a.n;
        this->matrix = a.matrix;
    }

    // a^k
    static Matrix matrix_pow(Matrix a, long long k, const long long mod = 0LL) {
        assert(a.m == a.n);
        const int n = a.m;

        Matrix b = Matrix::identity_matrix(n);
        while (k > 0) {
            if (k % 2 == 1) {
                b = Matrix::matrix_multiple(b, a, mod);
            }
            a = Matrix::matrix_multiple(a, a, mod);
            k /= 2;
        }
        return b;
    }

    // 行列式 O(n^3)
    double determinant(){
        assert(this->m == this->n);

        vector<vector<long long>> mat = this->matrix;
        std::vector<int> ri(n);
        std::iota(ri.begin(), ri.end(), 0);

        double det = 1.0;
        for (int p = 1 ; p <= n - 1; p++) {
            for (int i = p + 1 ; i <= n; i++) {
                if (std::abs(mat[ri[i - 1]][p - 1]) > std::abs(mat[ri[p - 1]][p - 1])) {
                    int t = ri[p - 1];
                    ri[p - 1] = ri[i - 1];
                    ri[i - 1] = t;
                    det = -det;
                }
            }
            if (mat[ri[p - 1]][p - 1] == 0) {
                return false;
            }

            det = det * mat[ri[p - 1]][p - 1];

            for (int i = p + 1 ; i <= n; i++) {
                mat[ri[i - 1]][p - 1] /= mat[ri[p - 1]][p - 1];

                for (int j = p + 1 ; j <= n; j++) {
                    mat[ri[i - 1]][j - 1] -= mat[ri[i - 1]][p - 1] * mat[ri[p - 1]][j - 1];
                }
            }
        }

        det = det * mat[ri[n - 1]][n - 1];
        return det;
    }

    void show() {
        for (int i = 0; i < this->m; ++i) {
            for (int j = 0; j < this->n; ++j) {
                if (j != 0) {
                    cout << " ";
                }
                cout << this->matrix[i][j];
            }
            cout << endl;
        }
    }
};

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

struct ChristmasBinaryTree {
    long long depth;
    vector<int> left;
    vector<int> right;
    int count(long long _depth, vector<int> _left, vector<int> _right) {
        depth = _depth, left = _left, right = _right;

        int N = LEN(left);
        Matrix m1(N, N);
        FOR(i, 0, N) {
            m1.matrix[i][left[i]] += 1;
            m1.matrix[i][right[i]] += 1;
        }

        m1.pow(depth - 1, MOD);

        LL ans = 0;
        FOR(i, 0, N) {
            LL tmp = 0;
            FOR(j, 0, N) {
                tmp += powmod(m1.matrix[i][j], 2, MOD);
                tmp %= MOD;
            }
            chmax(ans, tmp);
        }

        return ans;
    }
};

// CUT begin
ifstream data("../SRM 705_DIV2_900.sample");

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

bool do_test(long long depth, vector<int> left, vector<int> right, int __expected) {
    time_t startClock = clock();
    ChristmasBinaryTree *instance = new ChristmasBinaryTree();
    int __result = instance->count(depth, left, right);
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
        long long depth;
        from_stream(depth);
        vector<int> left;
        from_stream(left);
        vector<int> right;
        from_stream(right);
        next_line();
        int __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if ( do_test(depth, left, right, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1592125064;
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
        cout << "ChristmasBinaryTree (900 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
