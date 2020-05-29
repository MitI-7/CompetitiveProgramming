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

template<class T=long long> class Point {
public:
    T y;
    T x;
    Point() : y(0), x(0) {};
    Point(T y, T x) : y(y), x(x) {}

    // 内積 (dot product) : a⋅b = |a||b|cosθ
    static double dot(Point<T> a, Point<T> b) {
        return (a.y * b.y + a.x * b.x);
    }

    // 外積 (cross product) : a×b = |a||b|sinθ
    static double cross(Point<T> a, Point<T> b) {
        return (a.y * b.x - a.x * b.y);
    }

    Point<T> operator+(const Point<T> a) const {
        Point<T> res(*this);
        res.y += a.y;
        res.x += a.x;
        return res;
    }

    Point<T> operator-(const Point<T> a) const {
        Point<T> res(*this);
        res.y -= a.y;
        res.x -= a.x;
        return res;
    }
};

template<class T=long long> class Line {
public:
    Point<T> start;
    Point<T> end;

    Line() {};
    Line(Point<T> start, Point<T> end) : start(start), end(end) {}

    // line1とline2が並行かどうか判定する
    static bool is_parallel(const Line<T> &line1, const Line<T> &line2) {
        const auto y1 = line1.start.y - line1.end.y;
        const auto x1 = line1.start.x - line1.end.x;
        const auto y2 = line2.start.y - line2.end.y;
        const auto x2 = line2.start.x - line2.end.x;
        const auto p1 = Point<T>(y1, x1);
        const auto p2 = Point<T>(y2, x2);

        const auto a = p1.y * p2.x;
        const auto b = p1.x * p2.y;
        if (a > b) {
            return a - b <= EPS;
        }
        else {
            return b - a <= EPS;
        }
    }

    // line上にpointがあるか判定
    static bool on_line(const Point<T> &point, const Line<T> &line) {
        const auto ay = line.start.y; const auto ax = line.start.x;
        const auto by = line.end.y;  const auto bx = line.end.x;
        const auto cy = point.y; const auto cx = point.x;

        const auto l1 = (bx - ax) * (bx - ax) + (by - ay) * (by - ay);
        const auto l2 = (cx - ax) * (cx - ax) + (cy - ay) * (cy - ay);
        const auto c = (bx - ax) * (cx - ax) + (by - ay) * (cy - ay);
        return c >= 0 and c * c == l1 * l2 and l1 >= l2;
    };

    // line1とline2が交わっているか判定する
    static bool cross(const Line<T> &line1, const Line<T> &line2) {
        T ay1 = line1.start.y;
        T ax1 = line1.start.x;
        T ay2 = line1.end.y;
        T ax2 = line1.end.x;
        T by1 = line2.start.y;
        T bx1 = line2.start.x;
        T by2 = line2.end.y;
        T bx2 = line2.end.x;

        const auto ta = (bx1 - bx2) * (ay1 - by1) + (by1 - by2) * (bx1 - ax1);
        const auto tb = (bx1 - bx2) * (ay2 - by1) + (by1 - by2) * (bx1 - ax2);
        const auto tc = (ax1 - ax2) * (by1 - ay1) + (ay1 - ay2) * (ax1 - bx1);
        const auto td = (ax1 - ax2) * (by2 - ay1) + (ay1 - ay2) * (ax1 - bx2);

        // 一方の線分上にもう一方の端点がのっている
        if (on_line(line1.start, line2) or on_line(line1.end, line2) or on_line(line2.start, line1) or on_line(line2.end, line1)) {
            return true;
        }

        // 端点を含まないで交わる
        // tc * td < 0 && ta * tb < 0
        bool a = (ta != 0 and tb != 0 and ((ta < 0) != (tb < 0)));
        bool b = (tc != 0 and td != 0 and ((tc < 0) != (td < 0)));

        return a and b;
    }
};


struct CutCutCut {
    vector<int> X1;
    vector<int> Y1;
    vector<int> X2;
    vector<int> Y2;
    int Q;
    vector<int> findPieces(vector<int> _X1, vector<int> _Y1, vector<int> _X2, vector<int> _Y2, int _Q) {
        X1 = _X1, Y1 = _Y1, X2 = _X2, Y2 = _Y2, Q = _Q;

        auto ans = make_v<int>(0);
        ans.emplace_back(1);

        auto lines = make_v<Line<>>(0);
        lines.emplace_back(Line<>(Point<>(0, 0), Point<>(0, 10000)));
        lines.emplace_back(Line<>(Point<>(0, 0), Point<>(10000, 0)));
        lines.emplace_back(Line<>(Point<>(10000, 0), Point<>(10000, 10000)));
        lines.emplace_back(Line<>(Point<>(0, 10000), Point<>(10000, 10000)));

        FOR(i, 0, Q) {
            Line<> line(Point<>(Y1[i], X1[i]), Point<>(Y2[i], X2[i]));

            int num = 0;
            FOE(l, lines) {
                num += (Line<>::cross(l, line));
            }
            ans.emplace_back(ans.back() + num - 1);
            lines.emplace_back(line);
        }

        ans.erase(ans.begin());
        return ans;
    }
};

// CUT begin
ifstream data("../SRM 763_DIV1_250.sample");

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

template <typename T> string to_string(vector<T> ts) {
    stringstream s;
    s << "[ ";
    for (int i = 0; i < ts.size(); ++i) {
        if (i > 0) s << ", ";
        s << to_string(ts[i]);
    }
    s << " ]";
    return s.str();
}

bool do_test(vector<int> X1, vector<int> Y1, vector<int> X2, vector<int> Y2, int Q, vector<int> __expected) {
    time_t startClock = clock();
    CutCutCut *instance = new CutCutCut();
    vector<int> __result = instance->findPieces(X1, Y1, X2, Y2, Q);
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
        vector<int> X1;
        from_stream(X1);
        vector<int> Y1;
        from_stream(Y1);
        vector<int> X2;
        from_stream(X2);
        vector<int> Y2;
        from_stream(Y2);
        int Q;
        from_stream(Q);
        next_line();
        vector<int> __answer;
        from_stream(__answer);

        cases++;
        if (case_set.size() > 0 && case_set.find(cases - 1) == case_set.end())
            continue;

        cout << "  Testcase #" << cases - 1 << " ... ";
        if ( do_test(X1, Y1, X2, Y2, Q, __answer)) {
            passed++;
        }
    }
    if (mainProcess) {
        cout << endl << "Passed : " << passed << "/" << cases << " cases" << endl;
        int T = time(NULL) - 1589424761;
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
        cout << "CutCutCut (250 Points)" << endl << endl;
    }
    return run_test(mainProcess, cases, argv[0]);
}
// CUT end
