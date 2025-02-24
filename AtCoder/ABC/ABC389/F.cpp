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

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for (int i = (a); i < (n); ++i)
#define FOE(i, a) for (auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define BIT_COUNT32(bit) (__builtin_popcount(bit))
#define BIT_COUNT64(bit) (__builtin_popcountll(bit))

template<typename T> using MinPriorityQueue = std::priority_queue<T, std::vector<T>, std::greater<T>>;
template<typename T> using MaxPriorityQueue = std::priority_queue<T>;

// @formatter:off
typedef long long LL;
typedef __int128_t LLL;
template<typename T> std::vector<T> make_v(size_t a){return std::vector<T>(a);}
template<typename T,typename... Ts> auto make_v(size_t a, Ts... ts){ return std::vector<decltype(make_v<T>(ts...))>(a,make_v<T>(ts...));}    // C++14
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value==0>::type fill_v(T &t,const V &v){t=v;}
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value!=0>::type fill_v(T &t,const V &v){for(auto &e:t) fill_v(e,v);}
template<class T> inline T ceil(T a, T b) { return (a + b - 1) / b; }
void print() { std::cout << std::endl; }
template <class Head, class... Tail> void print(Head&& head, Tail&&... tail) { std::cout << head; if (sizeof...(tail) != 0) {std::cout << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void print(std::vector<T> &v) {for (auto& a : v) { std::cout << a; if (&a != &v.back()) {std::cout << " ";} }std::cout << std::endl;}
template <class T> void print(std::pair<T, T> &p) { std::cout << p.first << " " << p.second << std::endl; }
void debug() { std::cerr << std::endl; }
template <class Head, class... Tail> void debug(Head&& head, Tail&&... tail) { std::cerr << head; if (sizeof...(tail) != 0) {std::cerr << " ";} debug(std::forward<Tail>(tail)...); }
template <class T> void debug(std::vector<T> &v) {for (auto& a : v) { std::cerr << a; if (&a != &v.back()) {std::cerr << " ";} }std::cerr << std::endl;}
template <class T> void debug(std::pair<T, T> &p) { std::cerr << p.first << " " << p.second << std::endl; }
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
// @formatter:on

using namespace std;

// すべて 0-origin
template<class T>
class FenwickTree {
public:
    const int n;
    std::vector<T> v;

    // n: 要素数
    explicit FenwickTree(const int n) : n(n), v(n + 1, 0) {
    }

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

// 区間加算，区間和取得
// すべて 0-origin
template<typename T>
class FenwickTreeRange {
    FenwickTree<T> ft0, ft1;
public:
    const int n;
    explicit FenwickTreeRange(const int n) : n(n), ft0(n + 1), ft1(n + 1) {}

    // v[i]
    // O(log n)
    T access(const int i) const {
        assert(0 <= i and i < this->n);
        return this->sum(i, i + 1);
    }

    // v[i] += x
    // O(log n)
    void add(const int i, const T x) {
        assert(0 <= i and i < this->n);
        this->add(i, i + 1, x);
    }

    // v[left, right) += x
    // O(log n)
    void add(const int left, const int right, const T x) {
        if (left == right) {
            return;
        }
        assert(0 <= left and left < right and right <= this->n);
        this->ft0.add(left, x);
        this->ft0.add(right, -x);
        this->ft1.add(left, -x * left);
        this->ft1.add(right, x * right);
    }

    // v[left, right) += x
    // 加算位置が n 以上の場合は 0 に戻って加算される
    // O(log n)
    void add_circle(long long left, long long right, const T x) {
        assert(left < right);

        const long long num_loop = (right - left) / this->n;
        this->add(0, this->n, x * num_loop);

        // ループで終わり
        if ((right - left) % this->n == 0) {
            return;
        }

        left %= this->n;
        right %= this->n;

        if (left < right) {
            this->add(left, right, x);
        } else {
            this->add(left, this->n, x);
            this->add(0, right, x);
        }
    }

    // sum(v[0, i))
    // O(log n)
    T sum(const int i) const {
        assert(0 <= i and i <= this->n);
        return ft0.sum(i) * i + ft1.sum(i);
    }

    // sum(v[left, right))
    // O(log n)
    T sum(const int left, const int right) const {
        assert(0 <= left and left < right and right <= this->n);
        return this->sum(right) - this->sum(left);
    }

    // sum(v[left, right))
    // O(log n)
    T sum_circle(const int left, const int right) const {
        // TODO
        return 0;
    }

    void dump() {
        for (int i = 0; i < this->n; ++i) {
            if (i != 0) {
                std::cout << " ";
            }
            std::cout << this->access(i);
        }
        std::cout << std::endl;
    }
};

int lower_bound(int x, FenwickTreeRange<int> &ft) {
    auto ok = [&](int i) {
        return ft.access(i) >= x;
    };

    if (ft.access(0) >= x) {
        return 0;
    }

    if (ft.access(ft.n - 2) < x) {
        return ft.n - 1;
    }

    int left = 0, right = ft.n - 1;
    assert(not ok(left));
    assert(ok(right));
    while (right - left > 1) {
        const auto mid = std::midpoint(left, right);
        if (ok(mid)) {
            right = mid;
        } else {
            left = mid;
        }
    }
    return right;
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;

    FenwickTreeRange<int> ft(500100);
    FOR(i, 0, 500100) {
        ft.add(i, i);
    }
    FOR(i, 0, N) {
        int L, R;
        cin >> L >> R;
        int l = lower_bound(L, ft);
        int r = lower_bound(R + 1, ft);
        ft.add(l, r, 1);
    }

    int Q;
    cin >> Q;
    vector<LL> ans(Q);
    FOR(i, 0, Q) {
        int X;
        cin >> X;
        ans[i] = ft.access(X);
    }
    print(ans);

    return 0;
}
