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
bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }
unsigned long long bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) {
    assert(b == 0 or b == 1);
    if (b == 0) { return bit & ~(1ull << i); }
    else        {return bit | (1ull << i); }
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

using namespace std;


template <typename T=double> class Vector2D {
public:
    T x, y;

    Vector2D() {}
    Vector2D(double x, double y) : x(x), y(y) {}

    Vector2D operator+(const Vector2D p) {
        return Vector2D(x + p.x, y + p.y);
    }

    Vector2D operator-(const Vector2D p) {
        return Vector2D(x - p.x, y - p.y);
    }

    Vector2D operator*(const T d) {
        return Vector2D(d * x, d * y);
    }
    Vector2D operator/(const T d) {
        return Vector2D(x / d, y / d);
    }

    double norm() {
        return sqrt(x * x + y * y);
    }

    Vector2D rotate(double theta) {
        return Vector2D(x * cos(theta) - y * sin(theta), x * sin(theta) + y * cos(theta));
    }
};

template <typename T=double> class Circle {
public:
    Vector2D<T> center;    // 中心
    T radius;              // 半径

    Circle() {}
    Circle(Vector2D<T> center, double radius) : center(center), radius(radius) {}

    // 点pが円の中にあるか
    bool inside(Vector2D<T> p) {
        return (center - p).norm() < radius + EPS;  // 境界線上も含む
    }

    // 円の交点
    std::vector<Vector2D<T>> intersections(Circle<T> circle) {
        auto d = (circle.center - this->center).norm();
        auto rc = (this->radius * this->radius + d * d - circle.radius * circle.radius) / (2.0 * d);
        auto rs = sqrt(this->radius * this->radius - rc * rc);

        auto e1 = (circle.center - this->center) / d;
        auto e2 = e1.rotate(M_PI / 2);
        auto e3 = e1.rotate(-M_PI / 2);
        auto A = this->center + e1 * rc + e2 * rs;
        auto B = this->center + e1 * rc + e3 * rs;

        return {A, B};
    }

    // 円circleとの関係
    int intersect(const Circle &circle) {
        double dist = euclidean_distance(this->center.y, this->center.x, circle.point.y, circle.point.x);

        // 離れてる
        if(this->radius + circle.r < dist) { return 4; }
        // 外接
        if(eq(this->radius + circle.r, dist)) { return 3; }
        // 交わる
        if(this->radius - circle.r < dist) { return 2; }
        // 内接
        if(eq(this->radius - circle.r, dist)) { return 1; }

        // 内包
        return 0;
    }

    bool eq(T a, T b) {
        return abs(a - b) < EPS;
    }
};


LL K;
vector<tuple<double, double, double>> meat;

bool ok(double time) {
    int N = LEN(meat);

    auto circles = make_v<Circle<double>>(0);
    FOR(i, 0, N) {
        double x1, y1, c1;
        tie(x1, y1, c1) = meat[i];

        Circle circle1(Vector2D(x1, y1), time / c1);
        circles.emplace_back(circle1);
    }

    auto candidate_points = make_v<Vector2D<double>>(0);
    FOR(i, 0, N) {
        auto c1 = circles[i];
        candidate_points.emplace_back(c1.center);

        FOR(j, i + 1, N) {
            auto c2 = circles[j];
            auto a = c1.intersections(c2);

            FOR(k, 0, LEN(a)) {
                candidate_points.emplace_back(a[k]);
            }
        }
    }

    FOE(point, candidate_points) {
        int count = 0;
        FOE(c, circles) {
            count += c.inside(point);
        }
        if (count >= K) {
            return true;
        }
    }

    return false;
}

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);

    LL N;
    cin >> N >> K;
    meat = make_v<tuple<double, double, double>>(N);

    FOR(i, 0, N) {
        double X, Y, C;
        cin >> X >> Y >> C;
        meat[i] = make_tuple(X, Y, C);
    }

    double low = 0;
    double high = 10000000;
    FOR(i, 0, 1000) {
        double middle = (low + high) / 2.0;
        if (ok(middle)) {
            high = middle;
        }
        else {
            low = middle;
        }
    }
    printf("%.10f\n", high);

    return 0;
}