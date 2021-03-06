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

using LL = long long;
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

template <typename T> class SegmentTree {
    const int array_size;        // もとの配列のサイズ
    int n;
    std::vector<T> data;
    std::function<T (T,T)> op;
    T unit;

public:
    enum Mode {
        RangeMinimumQuery,
        RangeMaximumQuery,
        RangeSummationQuery,
    };

    SegmentTree(int array_size, Mode mode) : array_size(array_size) {
        if (mode == RangeMinimumQuery) {
            unit = INT_MAX;
            op = [](T a, T b) { return std::min(a, b); };
        }
        else if (mode == RangeMaximumQuery) {
            unit = 0;
            op = [](T a, T b) { return std::max(a, b); };
        }
        else if (mode == RangeSummationQuery) {
            unit = 0;
            op = [](T a, T b) { return a + b; };
        }
        else {
            assert(false);
        }

        n = 1;
        while (n < array_size) { n *= 2; }   // _n以上の最小の2冪
        data.resize(2 * n - 1, unit);
    }

    template <typename F> SegmentTree(int array_size, T unit, F op) : array_size(array_size), unit(unit), op(op) {
        while (n < array_size) { n *= 2; }   // _n以上の最小の2冪
        data.resize(2 * n - 1, unit);
    }

    T access(int idx) {
        return data[idx + n - 1];
    }

    // array[idx] = x
    // O(log N)
    void update(int idx, T x) {
        assert(0 <= idx and idx < array_size);
        idx += n - 1;   // 木での対象のインデックス
        data[idx] = x;
        while (idx > 0) {
            idx = (idx - 1) / 2;                                    // 親のインデックス
            data[idx] = op(data[idx * 2 + 1], data[idx * 2 + 2]);   // 左の子と右の子
        }
    }

    // op(array[left, right))
    // O(log N)
    T query(int left, int right) {
        assert(0 <= left and left < right and right <= array_size);
        return query(left, right, 0, 0, n);
    }

private:
    // [a, b)の目的値をノードk（区間[l, r]）から検索
    T query(int a, int b, int k, int l, int r) {
        assert(a < b && l < r);
        // 範囲外
        if (r <= a || b <= l) {
            return unit;
        }
        // 完全に含む
        if (a <= l && r <= b) {
            return this->data[k];
        }
            // 一部含む
        else {
            T vl = query(a, b, k * 2 + 1, l, (l + r) / 2);    // 左の子
            T vr = query(a, b, k * 2 + 2, (l + r) / 2, r);    // 右の子
            return op(vl, vr);
        }
    }
};


LL solve(int N, const vector<LL> &A, const vector<LL> &W) {
    auto v = make_v<pair<LL, LL>>(N);
    FOR(i, 0, N) {
        v[i] = make_pair(A[i], -i);
    }
    sort(ALL(v));

    map<LL, LL> m;
    FOR(i, 0, N) {
        m[-v[i].second] = i;
    }

    SegmentTree<LL> seg(N, SegmentTree<LL>::RangeMaximumQuery);

    auto dp = make_v<LL>(N + 1);
    dp[0] = W[0];
    seg.update(m[0], W[0]);

    LL ans = W[0];
    FOR(i, 1, N) {
        int idx = m[i];

        LL w = 0;
        if (idx > 0) {
            chmax(w, seg.query(0, idx);
        }
        chmax(dp[i], w + W[i]);
        seg.update(idx, dp[i]);

        chmax(ans, dp[i]);
    }

    return ans;
}


LL check(int N, const vector<LL> &A, const vector<LL> W) {
    auto dp = make_v<LL>(N + 1);
    dp[0] = W[0];
    LL ans = W[0];
    FOR(i, 1, N) {
        chmax(dp[i], W[i]);
        for (int j = i - 1; j >= 0; --j) {
            if (A[j] < A[i]) {
                chmax(dp[i], dp[j] + W[i]);
            }
        }
        chmax(ans, dp[i]);
    }

    return ans;
}

template<typename T> std::vector<T> make_random_vector(int n) {
    std::random_device rnd;
    std::mt19937 mt(rnd());
    std::vector<T> v(n);
    for (int i = 0; i < n; ++i) {
        v[i] = mt() % 10;
    }
    return v;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    int T;
    cin >> T;
    FOR(i, 0, T) {
        int N;
        cin >> N;
        auto A = make_v<LL>(N);
        auto W = make_v<LL>(N);
        FOR(j, 0, N) {
            cin >> A[j];
        }
        FOR(j, 0, N) {
            cin >> W[j];
        }

        print(solve(N, A, W));
    }

    return 0;
}