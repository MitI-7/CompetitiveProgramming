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

template<class T, T (*op)(T, T), T (*unit)()>
class SegmentTree {
    int n;// セグ木で使う配列のサイズ
    int array_size;
    std::vector<T> data;

public:
    SegmentTree(const int array_size) : n(1), array_size(array_size) {
        // n は array_size 以上の最小の 2 冪
        while (this->n < array_size) {
            this->n <<= 1;
        }
        this->data.resize(2 * this->n - 1, unit());
    }

    SegmentTree(const std::vector<T> &v) : n(1) {
        while (this->n < (int) v.size()) {
            this->n <<= 1;
        }
        this->data.resize(2 * this->n - 1, unit());

        for (int i = 0; i < this->array_size; ++i) {
            this->data[i + n - 1] = v[i];
        }

        for (int u = this->n - 2; u >= 0; --u) {
            this->data[u] = op(this->data[u * 2 + 1], this->data[u * 2 + 2]);
        }
    }

    T access(const int idx) const {
        return this->data[idx + this->n - 1];
    }

    // data[idx] = x
    // O(log N)
    void update(int idx, const T x) {
        assert(0 <= idx and idx < this->array_size);
        idx += this->n - 1;// 木での対象のインデックス
        this->data[idx] = x;
        while (idx > 0) {
            idx = (idx - 1) / 2;                                                   // 親のインデックス
            this->data[idx] = op(this->data[idx * 2 + 1], this->data[idx * 2 + 2]);// 左の子と右の子
        }
    }

    // op(data[left, right))
    // O(log N)
    T query(const int left, const int right) const {
        assert(0 <= left and left <= right and right <= this->array_size);
        return query(left, right, 0, 0, this->n);
    }

    T query() const {
        return query(0, this->array_size, 0, 0, this->n);
    }

private:
    // 区間 [l, r)の値をノード u から検索
    // ノード u は[start, end) をカバーする
    T query(const int l, const int r, const int u, const int start, const int end) const {
        assert(l < r && start < end);
        // 範囲外
        if (end <= l or r <= start) {
            return unit();
        }

        // 完全に含む
        if (l <= start and end <= r) {
            return this->data[u];
        } else {
            const int m = (start + end) / 2;
            auto vl = query(l, r, u * 2 + 1, start, m);// 左の子
            auto vr = query(l, r, u * 2 + 2, m, end);  // 右の子
            return op(vl, vr);
        }
    }
};

// 区間 max
template<typename T>
T op(T a, T b) {
    return std::max(a, b);
}

template<typename T>
T unit() {
    return 0;
}

template<typename T>
SegmentTree<T, op, unit> make_segment_tree(const int n) {
    return SegmentTree<T, op, unit>(n);
}


template<typename T> class LineQuery {
public:
    int N;
    SegmentTree<T, op, unit> st;
    LineQuery(int N) : N(N), st(N) {
    }

    void set(int i, int x) {
        this->st.update(i, x);
    }

    // [l, r) にある x 以上の要素で一番左のインデックス
    // 存在しない場合は -1 を返す
    int left(const int l, const int r, const int x) const {
        assert(0 <= l and l <= r and r <= this->N);
        if (this->st.query(l, r) < x) {
            return -1;
        }

        if (this->st.access(l) >= x) {
            return l;
        }

        int low = l;
        int high = r;
        while (high - low > 1) {
            const auto middle = (low + high) / 2;
            if (this->st.query(l, middle) >= x) {
                high = middle;
            } else {
                low = middle;
            }
        }
        return low;
    }

    // [l, r) にある x 以上の要素で一番右のインデックス
    // 存在しない場合は -1 を返す
    int right(const int l, const int r, const int x) const {
        assert(0 <= l and l <= r and r <= this->N);
        if (this->st.query(l, r) < x) {
            return -1;
        }
        if (this->st.access(r - 1) >= x) {
            return r - 1;
        }

        int low = l;
        int high = r;
        while (high - low > 1) {
            const auto middle = (low + high) / 2;
            if (this->st.query(middle, r) >= x) {
                low = middle;
            } else {
                high = middle;
            }
        }

        return low;
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;
    vector<long long> P(N + 4);
    for (int i = 0; i < N; ++i) {
        cin >> P[i + 2];
    }
    P[0] = INF + 1;
    P[1] = INF;
    P[N + 2] = INF + 2;
    P[N + 3] = INF + 3;

    long long ans = 0;
    FOR(_, 0, 2) {
        LineQuery<int> lq(N + 4);
        for (int i = 0; i < N + 4; ++i) {
            lq.set(i, P[i]);
        }

        for (int i = 2; i < N + 2; ++i) {
            const int a = lq.right(0, i, P[i]);
            if (a == 1) {
                continue;
            }
            const int l = lq.right(0, a, P[i]);
            const int r = lq.left(i + 1, N + 4, P[i]);
            ans += (a - l) * (r - i) * P[i];
        }
        reverse(ALL(P));
    }
    cout << ans << endl;

    return 0;
}
