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

template<class T> inline std::vector<T> unique(std::vector<T> v) {
    sort(v.begin(), v.end());
    v.erase(unique(v.begin(), v.end()), v.end());
    return v;
}

// 初項s交差d長さnの数列の和
long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}

// xが2の階乗かどうか判定
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

const int INF = 1u << 30u;  // 1,073,741,824
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
const std::vector<int> dy2 = {0, 1}, dx2 = {1, 0};
const std::vector<int> dy4 = {0, 1, 0, -1}, dx4 = {1, 0, -1, 0};
const std::vector<int> dy8 = {0, -1, 0, 1, 1, -1, -1, 1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};

class Point {
public:
    double x;
    double y;

    Point(): x(0), y(0) {}
    Point(double x, double y) : x(x), y(y) {}
};

class SmallestEnclosingCircle {
private:
    double min_x;
    double max_x;
    double min_y;
    double max_y;

public:
    SmallestEnclosingCircle() {}

    // 最小包含円の半径
    double solve(const std::vector<Point> &points) {
        this->min_x = this->max_x = points[0].x;
        this->min_y = this->max_y = points[0].y;

        for (const auto &p : points) {
            this->min_x = std::min(this->min_x, p.x);
            this->max_x = std::max(this->max_x, p.x);
            this->min_y = std::min(this->min_y, p.y);
            this->max_y = std::max(this->max_y, p.y);
        }

        double l = this->min_x - 1.0;
        double r = this->max_x + 1.0;

        // x座標で3分探索
        for (int _ = 0; _ < 100; ++_) {
            const double c1 = (l * 2 + r) / 3.0;
            const double c2 = (l + r * 2) / 3.0;

            if (g(c1, points) > g(c2, points)) {
                l = c1;
            } else {
                r = c2;
            }
        }

        return g(l, points);
    }

private:

    // 点aと点bの距離
    double dist(const Point &a, const Point &b) {
        double dx = a.x - b.x;
        double dy = a.y - b.y;
        return sqrt(dx * dx + dy * dy);
    }

    // nowから最も遠い点までの距離
    double max_distance(const Point &now, const std::vector<Point> &points) {
        double res = 0;
        for (const auto p : points) {
            res = std::max(res, dist(now, p));
        }
        return res;
    }

    // x座標を決めたときの，y軸の距離を最小化
    double g(const double x, const std::vector<Point> &points) {
        double l = this->min_y - 1.0;
        double r = this->max_y + 1.0;

        for (int _ = 0; _ < 100; ++_) {
            double c1 = (l * 2 + r) / 3;
            double c2 = (l + r * 2) / 3;

            if (max_distance(Point(x, c1), points) > max_distance(Point(x, c2), points)) {
                l = c1;
            } else {
                r = c2;
            }
        }

        return max_distance(Point(x, l), points);
    }
};

using namespace std;

// iさんをhole[j]に割り当てられるか
bool can_assign(int i, int j, vector<bool> &used, vector<double> &holes, vector<double> &dists) {
    vector<double> rest_dists;
    for (int k = i + 1; k < dists.size(); ++k) {
        rest_dists.emplace_back(dists[k]);
    }
    sort(rest_dists.rbegin(), rest_dists.rend());

    vector<double> rest_holes;
    for (int k = 0; k < (int)holes.size(); ++k) {
        if (k != j and not used[k]) {
            rest_holes.emplace_back(holes[k]);
        }
    }
    sort(rest_holes.rbegin(), rest_holes.rend());

    assert(rest_holes.size() >= rest_dists.size());
    for (int k = 0; k < rest_dists.size(); ++k) {
        if (rest_holes[k] < rest_dists[k]) {
            return false;
        }
    }

    return true;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    int N, M;
    cin >> N >> M;
    vector<double> holes(N);
    for (int i = 0; i < N; ++i) {
        cin >> holes[i];
    }

    vector<double> dist(M);
    for (int i = 0; i < M; ++i) {
        int P;
        cin >> P;
        vector<Point> points(P);

        for (int j = 0; j < P; ++j) {
            cin >> points[j].x >> points[j].y;
        }

        SmallestEnclosingCircle sec;
        dist[i] = sec.solve(points) - EPS;
    }

    vector<int> ans(M, -1);
    vector<bool> used(N);
    for (int i = 0; i < M; ++i) {
        for (int j = 0; j < N; ++j) {
            if (not used[j] and dist[i] <= holes[j]) {
                if (can_assign(i, j, used, holes, dist)) {
                    ans[i] = j;
                    used[j] = true;
                    break;
                }
            }
        }
        if (ans[i] == -1) {
            cout << "NG" << endl;
            return 0;
        }
    }

    for (int i = 0; i < M; ++i) {
        cout << ans[i] + 1 << endl;
    }

    return 0;
}