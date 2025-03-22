#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cmath>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

// clang-format off
#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for (int i = (a); i < (n); ++i)
#define FOE(i, a) for (auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define BIT_COUNT32(bit) (__builtin_popcount(bit))
#define BIT_COUNT64(bit) (__builtin_popcountll(bit))

template<typename T> using MinPriorityQueue = std::priority_queue<T, std::vector<T>, std::greater<T>>;
template<typename T> using MaxPriorityQueue = std::priority_queue<T>;

typedef long long LL;
typedef __int128_t LLL;
template<typename T> std::vector<T> make_v(size_t a){return std::vector<T>(a);}
template<typename T,typename... Ts> auto make_v(size_t a, Ts... ts){ return std::vector<decltype(make_v<T>(ts...))>(a,make_v<T>(ts...));}    // C++14
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value==0>::type fill_v(T &t,const V &v){t=v;}
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value!=0>::type fill_v(T &t,const V &v){for(auto &e:t) fill_v(e,v);}
template<class T> inline T ceil(T a, T b) { return (a + b - 1) / b; }
void print() { std::cout << "\n"; }
template <class Head, class... Tail> void print(Head&& head, Tail&&... tail) { std::cout << head; if (sizeof...(tail) != 0) {std::cout << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void print(std::vector<T> &v) {for (auto& a : v) { std::cout << a; if (&a != &v.back()) {std::cout << " ";} }std::cout << "\n";}
template <class T> void print(std::pair<T, T> &p) { std::cout << p.first << " " << p.second << "\n"; }
void debug() { std::cerr << "\n"; }
template <class Head, class... Tail> void debug(Head&& head, Tail&&... tail) { std::cerr << head; if (sizeof...(tail) != 0) {std::cerr << " ";} debug(std::forward<Tail>(tail)...); }
template <class T> void debug(std::vector<T> &v) {for (auto& a : v) { std::cerr << a; if (&a != &v.back()) {std::cerr << " ";} }std::cerr << "\n";}
template <class T> void debug(std::pair<T, T> &p) { std::cerr << p.first << " " << p.second << "\n"; }
inline bool inside(long long y, long long x, long long H, long long W) {return 0 <= y and y < H and 0 <= x and x < W; }
template<class T> inline double euclidean_distance(T y1, T x1, T y2, T x2) { return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)); }
template<class T> inline T euclidean_distance2(T y1, T x1, T y2, T x2) { return (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2); }
template<class T> inline T manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }
template<typename T> T &chmin(T &a, const T &b) { return a = std::min(a, b); }
template<typename T> T &chmax(T &a, const T &b) { return a = std::max(a, b); }
bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }
unsigned long long get_bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) { assert(b == 0 or b == 1); if (b == 0) { return bit & ~(1ull << i); } else {return bit | (1ull << i);}}

const int INF = 1u << 30u;  // 1,073,741,824
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
// 2次元配列上での移動．右，下，左，上，右上，右下，左下，左上
const std::vector<int> dy8 = {0, 1, 0, -1, -1, 1, 1, -1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};
// clang-format on

using namespace std;

// 1次式　ax + b
template<typename T>
class LinearExpression {
public:
    T a;
    T b;

    LinearExpression(T a = 0, T b = 0) : a(a), b(b) {}

    T evaluate(T x) const {
        return this->a * x + this->b;
    }

    // ax + b == cx + d のとき，x を求める
    T find_x(const LinearExpression &obj) const {
        return (obj.b - this->b) / (this->a - obj.a);
    }

    LinearExpression operator+(const LinearExpression &obj) const {
        return LinearExpression(this->a + obj.a, this->b + obj.b);
    }

    LinearExpression &operator+=(const LinearExpression &obj) {
        this->a += obj.a;
        this->b += obj.b;
        return *this;
    }

    LinearExpression operator-(const LinearExpression &obj) const {
        return LinearExpression(a - obj.a, b - obj.b);
    }

    LinearExpression &operator-=(const LinearExpression &obj) {
        this->a - obj.a;
        this->b - obj.b;
        return *this;
    }

    LinearExpression operator*(const T c) const {
        return LinearExpression(a * c, b * c);
    }

    LinearExpression &operator*=(const T c) {
        this->a *= c;
        this->b *= c;
        return *this;
    }

    LinearExpression operator/(const T c) const {
        return LinearExpression(a / c, b / c);
    }

    LinearExpression &operator/=(const T c) {
        this->a /= c;
        this->b /= c;
        return *this;
    }

    bool operator==(const LinearExpression &obj) const {
        return this->a == obj.a and this->b == obj.b;
    }

    friend std::ostream &operator<<(std::ostream &os, const LinearExpression &obj) {
        os << obj.a << "x" << " + " << obj.b;
        return os;
    }
};

// #include <cassert>
// #include <vector>

// すべて 0-origin
template<class T>
class FenwickTree {
public:
    const int n;
    std::vector<T> v;

    // n: 要素数
    explicit FenwickTree(const int n) : n(n), v(n + 1, 0) {}

    // v[i]
    // O(log n)
    T access(const int i) const {
        return this->sum(i, i + 1);
    }

    // v[i] += x
    // O(log n)
    void add(int i, const T x) {
        assert(i < this->n);

        while (i < this->n) {
            this->v[i] += x;
            i |= i + 1;
        }
    }

    // v[i] = x
    // O(log n)
    void update(const int i, const T x) {
        assert(i < this->n);

        const T now = this->access(i);
        this->add(i, x - now);
    }

    // sum(v[0, i))
    // O(log n)
    T sum(int i) const {
        assert(0 <= i and i <= this->n);

        T s = 0;
        i -= 1;
        while (i >= 0) {
            s += this->v[i];
            i = (i & (i + 1)) - 1;
        }
        return s;
    }

    // sum(v[left, right))
    // O(log n)
    T sum(const int left, const int right) const {
        if (left >= right) {
            return 0;
        }
        return this->sum(right) - this->sum(left);
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, M, K;
    cin >> N >> M >> K;

    FenwickTree<LinearExpression<double>> ft(N + M + 10);
    int last = -INF;
    int num = 0;
    vector<int> ng(N + 1);
    FOR(i, 0, K) {
        int A;
        cin >> A;
        ng[A] = 1;
        ft.update(A, LinearExpression<double>(1, 0));

        if (last + 1 == A) {
            num++;
        } else {
            num = 1;
        }

        if (num >= M) {
            print(-1);
            return 0;
        }
        last = A;
    }

    for (int i = N - 1; i >= 0; --i) {
        if (ng[i]) {
            continue;
        }
        auto t = ft.sum(i + 1, i + M + 1);
        ft.update(i, t / M + LinearExpression<double>(0, 1));
    }

    const auto ans = ft.access(0).find_x(LinearExpression<double>(1, 0));
    cout << setprecision(10) << fixed << ans << endl;

    return 0;
}
