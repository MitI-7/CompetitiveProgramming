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
// clang-format on

using namespace std;

// #include <cassert>
// #include <functional>
// #include <numeric>
// #include <vector>

template<typename S, typename F, S (*op)(S, S), S (*mapping)(S, F, int), F (*composition)(F, F), S (*unit)(), F (*lazy_unit)()>
class LazySegmentTree {
private:
    int n;
    int array_size;
    std::vector<S> data;
    std::vector<F> lazy;

public:
    LazySegmentTree(const int array_size, const S initial_value) : n(1), array_size(array_size) {
        while (this->n < array_size) {
            this->n <<= 1;
        }
        this->data.resize(2 * this->n - 1);
        this->lazy.resize(2 * this->n - 1, lazy_unit());

        for (int u = 0; u < array_size; ++u) {
            this->data[this->n - 1 + u] = initial_value;
        }
        for (int u = this->n - 2; u >= 0; --u) {
            this->data[u] = op(this->data[u * 2 + 1], this->data[u * 2 + 2]);
        }
    }

    explicit LazySegmentTree(const std::vector<S> &v) : n(1), array_size(v.size()) {
        while (this->n < (int) v.size()) {
            this->n <<= 1;
        }
        this->data.resize(2 * this->n - 1);
        this->lazy.resize(2 * this->n - 1, lazy_unit());

        for (int u = 0; u < (int) v.size(); ++u) {
            this->data[this->n - 1 + u] = v[u];
        }
        for (int u = this->n - 2; u >= 0; --u) {
            this->data[u] = op(this->data[u * 2 + 1], this->data[u * 2 + 2]);
        }
    }

    // array[idx]
    // log(N)
    S access(const int idx) {
        assert(0 <= idx and idx < this->array_size);
        return this->query(idx, idx + 1);
    }

    // idx に x を適用する
    // log(N)
    void operation(const int idx, const F x) {
        assert(0 <= idx and idx < this->array_size);
        this->operation(idx, idx + 1, x);
    }

    // 区間 [left, right) に x を適用する
    // log(N)
    void operation(const int left, const int right, const F x) {
        assert(left <= right and 0 <= left and right <= this->array_size);
        this->operation(left, right, x, 0, 0, this->n);
    }

    // 区間 [left, right) から値を求める
    // log(N)
    S query(const int left, const int right) {
        assert(0 <= left and left <= right and right <= this->array_size);
        return this->query(left, right, 0, 0, this->n);
    }

    // 全区間から値を求める
    // log(N)
    S query() {
        return this->query(0, this->array_size, 0, 0, this->n);
    }

private:
    // 区間 [l, r) に x を適用する
    // ノード u は[start, end) をカバーする
    // ノード u の値を返す
    S operation(const int l, const int r, const F x, const int u, const int start, const int end) {
        this->propagate(u, end - start);

        // 範囲外
        if (r <= start or end <= l) {
            // 更新なので上の子は data[u] が必要
            return this->data[u];
        }

        // 完全に含むので遅延更新
        if (l <= start and end <= r) {
            this->lazy[u] = composition(this->lazy[u], x);
            this->propagate(u, end - start);
            return this->data[u] = mapping(this->data[u], this->lazy[u], end - start);
        }

        // 部分的に含む
        const auto m = (start + end) / 2;
        const auto lv = this->operation(l, r, x, 2 * u + 1, start, m); // 左の子
        const auto rv = this->operation(l, r, x, 2 * u + 2, m, end); // 右の子
        return this->data[u] = op(lv, rv);
    }

    // 区間 [l, r) から値を検索する
    // ノード u は[start, end) をカバーする
    S query(const int l, const int r, const int u, const int start, const int end) {
        this->propagate(u, end - start);

        // 範囲外
        if (r <= start or end <= l) {
            return unit();
        }

        // 完全に含む
        if (l <= start and end <= r) {
            return this->data[u];
        }

        // 一部含む
        const auto m = (start + end) / 2;
        const auto vl = this->query(l, r, u * 2 + 1, start, m); // 左の子
        const auto vr = this->query(l, r, u * 2 + 2, m, end); // 右の子
        return op(vl, vr);
    }

    // u の値を更新し，u の子供に遅延情報を伝える
    void propagate(const int u, const int len) {
        // 伝播済み
        if (this->lazy[u] == lazy_unit()) {
            return;
        }

        if (len > 1) {
            this->lazy[u * 2 + 1] = composition(this->lazy[u * 2 + 1], this->lazy[u]);
            this->lazy[u * 2 + 2] = composition(this->lazy[u * 2 + 2], this->lazy[u]);
        }
        this->data[u] = mapping(this->data[u], this->lazy[u], len);
        this->lazy[u] = lazy_unit();
    }
};

// 区間合計，区間更新
namespace range_sum_range_update {
    template<typename S>
    S unit() {
        return 0;
    }

    template<typename F>
    F lazy_unit() {
        return std::numeric_limits<F>::max() / 3;
    }

    template<typename S>
    S op(const S left_value, const S right_value) {
        return left_value + right_value;
    }

    template<typename S, typename F>
    S mapping(const S value, const F lazy_value, const int len) {
        if (lazy_value == lazy_unit<S>()) {
            return value;
        }
        return lazy_value * len;
    }

    template<typename F>
    F composition(const F old_lazy_value, const F new_lazy_value) {
        if (new_lazy_value == lazy_unit<F>()) {
            return old_lazy_value;
        }
        return new_lazy_value;
    }

    template<typename S>
    auto make_lazy_segment_tree(const int n, const S initial_value) {
        return LazySegmentTree<S, S, op, mapping, composition, unit, lazy_unit>(n, initial_value);
    }

    template<typename S>
    auto make_lazy_segment_tree(const std::vector<S> &v) {
        return LazySegmentTree<S, S, op, mapping, composition, unit, lazy_unit>(v);
    }
} // namespace range_sum_range_update


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, Q, X;
    cin >> N >> Q >> X;
    vector<int> P(N);
    FOR(i, 0, N) {
        cin >> P[i];
        if (P[i] < X) {
            P[i] = 0;
        } else if (P[i] == X) {
            P[i] = 1;
        } else {
            P[i] = 2;
        }
    }

    auto lst = range_sum_range_update::make_lazy_segment_tree(P);

    FOR(i, 0, Q) {
        int C, L, R;
        cin >> C >> L >> R;
        L--;

        int num_x = 0, num_lt_x = 0, num_gt_x = 0;
        int s = lst.query(L, R);
        if (s % 2 == 1) {
            num_x = 1;
            s -= 1;
        }
        num_gt_x = s / 2;
        num_lt_x = (R - L) - num_x - num_gt_x;

        if (C == 1) {
            // 昇順(x未満，x，xより大)
            lst.operation(L, L + num_lt_x, 0);
            lst.operation(L + num_lt_x, L + num_lt_x + num_x, 1);
            lst.operation(L + num_lt_x + num_x, L + num_lt_x + num_x + num_gt_x, 2);
        } else if (C == 2) {
            // 降順(xより大，x，x未満)
            lst.operation(L, L + num_gt_x, 2);
            lst.operation(L + num_gt_x, L + num_gt_x + num_x, 1);
            lst.operation(L + num_gt_x + num_x, L + num_gt_x + num_x + num_lt_x, 0);
        } else {
            assert(false);
        }
    }

    FOR(i, 0, N) {
        if (lst.access(i) == 1) {
            print(i + 1);
        }
    }

    return 0;
}
