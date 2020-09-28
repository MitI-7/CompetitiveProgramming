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

template <typename T> class LazySegmentTree {
private:
    const int array_size;
    int n;
    std::vector<T> data, lazy;
    const function<T (T, T)> f;     // 要素に適用する演算
    const function<T (T, T)> g;     // 作用素の適用
    const function<T (T, T)> h;     // 作用素の合成
    const function<T (T, int)> p;
    const T unit;
    const T lazy_unit;

public:
    class Mode {
    public:
        function<T (T, T)> f;
        function<T (T, T)> g;
        function<T (T, T)> h;
        function<T (T, int)> p;
        T unit;
        T lazy_unit;
    };

    enum Query {
        RangeMinimumQuery,
        RangeMaximumQuery,
        RangeSummationQuery,
    };

    enum Operation {
        Update,
        Add,
    };

    LazySegmentTree(const std::vector<LL> &v, const Mode mode) : array_size(v.size()),  f(mode.f), g(mode.g), h(mode.h), p(mode.p), unit(mode.unit), lazy_unit(mode.lazy_unit){
        n = 1;
        while (n < array_size) { n *= 2; }
        data.resize(2 * n - 1, unit);
        lazy.resize(2 * n - 1, lazy_unit);

        for (int i = 0; i < array_size; ++i) {
            data[i + n - 1] = v[i];
        }
        for (int i = n - 2; i >= 0; i--) {
            data[i] = f(data[i * 2 + 1], data[i * 2 + 2]);
        }
    }

    static Mode getMode(const Query query, const Operation operation) {
        Mode mode;
        if (query == RangeMinimumQuery) {
            mode.unit = INT_MAX;

            mode.f = [](T a, T b) { return std::min(a, b); };
            if (operation == Update) {
                mode.lazy_unit = -1;
                mode.g = [&](T a, T b) { return b == mode.lazy_unit ? a : b; };
                mode.h = mode.g;
                mode.p = [&](T a, int len) { return a; };
            }
            else if (operation == Add) {
                mode.lazy_unit = 0;
                mode.g = [](T a, T b) { return a + b; };
                mode.h = mode.g;
                mode.p = [](T a, int len) { return a; };
            }
        }
        else if (query == RangeMaximumQuery) {
            mode.unit = -INT_MAX;

            mode.f = [](T a, T b) { return std::max(a, b); };
            if (operation == Update) {
                mode.lazy_unit = -1;
                mode.g = [&](T a, T b) { return b == mode.lazy_unit ? a : b; };
                mode.h = mode.g;
                mode.p = [](T a, int len) { return a; };
            }
            else if (operation == Add) {
                mode.lazy_unit = 0;
                mode.g = [](T a, T b) { return a + b; };
                mode.h = mode.g;
                mode.p = [](T a, int len) { return a; };
            }
        }
        else if (query == RangeSummationQuery) {
            mode.unit = 0;

            mode.f = [](T a, T b) { return a + b; };
            if (operation == Update) {
                mode.lazy_unit = INT_MAX;
                mode.g = [&](T a, T b) { return b == mode.lazy_unit ? a : b;};
                mode.h = mode.g;
                mode.p = [&](T a, int len) {return a == mode.lazy_unit ? a : a * len;};
            }
            else if (operation == Add) {
                mode.lazy_unit = 0;
                mode.g = [](T a, T b) { return a + b;};
                mode.h = [](T a, T b) { return a + b;};
                mode.p = [](T a, int len) {return a * len;};
            }
        }
        return mode;
    }

    // array[idx]
    // log(N)
    T access(const int idx) {
        return query(idx, idx + 1, 0, 0, n);
    }

    // operation(array[idx], x)
    // log(N)
    void operation(const int idx, const T x) {
        operation(idx, idx + 1, x);
    }

    // operation(array[left, right), x)
    // log(N)
    void operation(const int left, const int right, const T x) {
        assert(0 <= left and left < right and right <= array_size);
        operation(left, right, x, 0, 0, n);
    }

    // op(array[a, b))
    // log(N)
    T query(const int left, const int right) {
        return query(left, right, 0, 0, n);
    }

private:
    T operation(const int a, const int b, const T x, const int k, const int l, const int r) {
        propagate(k, r - l);

        // 範囲外
        if (b <= l or r <= a) {
            return data[k];
        }
        // 完全に含む
        else if (a <= l and r <= b) {
            lazy[k] = h(lazy[k], x);
            propagate(k, r - l);
            return g(data[k], p(lazy[k], r - l));
        }
        // 一部含む
        else {
            T lv = operation(a, b, x, 2 * k + 1, l, (l + r) / 2);    // 左の子
            T rv = operation(a, b, x, 2 * k + 2, (l + r) / 2, r);    // 右の子
            return data[k] = f(lv, rv);
        }
    }

    // [a, b)の目的値をノードk（区間[l, r]）から検索
    T query(const int a, const int b, const int k, const int l, const int r) {
        propagate(k, r - l);

        // 範囲外
        if (b <= l or r <= a) {
            return unit;
        }
        // 完全に含む
        else if (a <= l && r <= b) {
            return data[k];
        }
        // 一部含む
        else {
            T vl = query(a, b, k * 2 + 1, l, (l + r) / 2);    // 左の子
            T vr = query(a, b, k * 2 + 2, (l + r) / 2, r);    // 右の子
            return f(vl, vr);
        }
    }

    void propagate(const int k, const int len) {
        if (lazy[k] == lazy_unit) {
            return;
        }

        if (len > 1) {
            lazy[k * 2 + 1] = h(lazy[k * 2 + 1], lazy[k]);
            lazy[k * 2 + 2] = h(lazy[k * 2 + 2], lazy[k]);
        }
        data[k] = g(data[k], p(lazy[k], len));
        lazy[k] = lazy_unit;
    }
};

template<class T> class BisectWrapper {
public:
    // aにxが存在するか
    bool exist(const std::vector<T> &a, T x) {
        return binary_search(a.begin(), a.end(), x);
    }

    // xのindex(なければ-1)
    int index(const std::vector<T> &a, T x) {
        auto i = lower_bound(a.begin(), a.end(), x);
        if (i != a.end() and a[i] == x) {
            return distance(a.begin(), i);
        }
    }

    // y < xのようなyの中でもっとも右のindex
    // なければ-1
    int index_lt(const std::vector<T> &a, T x) {
        auto i = lower_bound(a.begin(), a.end(), x);
        return distance(a.begin(), i) - 1;
    }

    // x未満の個数
    int count_lt(const std::vector<T> &a, T x) {
        return lower_bound(a.begin(), a.end(), x) - a.begin();
    }

    // y <= xのようなyの中でもっとも右のindex
    int index_lte(const std::vector<T> &a, T x) {
        auto i = lower_bound(a.begin(), a.end(), x);
        if (i == a.end()) {
            return a.size() - 1;
        }
        // y == x
        if (*i == x) {
            return distance(a.begin(), i);
        }
        else {
            return distance(a.begin(), i) - 1;
        }
    }

    // x以下の個数
    int count_lte(const std::vector<T> &a, T x) {
        return upper_bound(a.begin(), a.end(), x) - a.begin();
    }

    // y > xのようなyの中でもっとも左のindex
    // なければN
    int index_gt(const std::vector<T> &a, T x) {
        auto i = upper_bound(a.begin(), a.end(), x);
        return distance(a.begin(), i);
    }

    // xより大きい個数
    int count_gt(const std::vector<T> &a, T x) {
        return a.end() - upper_bound(a.begin(), a.end(), x);
    }

    // y >= xのようなyの中でもっとも左のindex
    int index_gte(const std::vector<T> &a, T x) {
        auto i = lower_bound(a.begin(), a.end(), x);
        return distance(a.begin(), i);
    }

    // x以上の個数
    int count_gte(const std::vector<T> &a, T x) {
        return a.end() - lower_bound(a.begin(), a.end(), x);
    }

    // [x, y)に入る要素の個数
    int count(const std::vector<T> &a, T x, T y) {
        return this->count_lt(a, y) - this->count_lt(a, x);
    }
};

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);

    LL N, D, A;
    cin >> N >> D >> A;

    auto X_H = make_v<pair<LL, LL>>(N);
    FOR(i, 0, N) {
        cin >> X_H[i].first >> X_H[i].second;
    }
    sort(ALL(X_H));

    auto X = make_v<LL>(N);
    auto H = make_v<LL>(N);
    FOR(i, 0, N) {
        X[i] = X_H[i].first;
        H[i] = X_H[i].second;
    }

    auto mode = LazySegmentTree<LL>::getMode(LazySegmentTree<LL>::RangeMinimumQuery, LazySegmentTree<LL>::Add);
    LazySegmentTree<LL> lst(H, mode);

    BisectWrapper<LL> bw;
    LL ans = 0;
    FOR(i, 0, N) {
        const LL now_h = lst.access(i);
        if (now_h > 0) {
            LL num = ceil(now_h, A);
            LL left_idx = i;
            LL right_idx = bw.index_lte(X, X[i] + D * 2);
            lst.operation(left_idx, right_idx + 1, -num * A);
            ans += num;
        }
    }

    print(ans);

    return 0;
}
