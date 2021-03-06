#include <iostream>
#include <array>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <cmath>
#include <string>
#include <climits>
#include <cassert>
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


int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    LL N, M;
    string S;
    cin >> N >> M;
    cin >> S;

    SegmentTree<LL> seg(N + 1, SegmentTree<LL>::RangeMinimumQuery);
    FOR(i, 0, N) {
        seg.update(i, INF);
    }
    seg.update(N, 0);

    auto dp = make_v<LL>(N + 1);
    fill_v(dp, INF);
    dp[N] = 0;
    for (int i = N - 1; i >= 0; --i) {
        if (S[i] == '1') {
            continue;
        }
        auto m = seg.query(i + 1, min(N + 1, i + M + 1));
        seg.update(i, m + 1);
        dp[i] = m + 1;
    }

    auto now = seg.access(0);
    if (now >= INF) {
        print(-1);
        return 0;
    }

    auto ans = make_v<LL>(0);
    int step = 0;
    while (step < N) {
        FOR(i, step + 1, N + 1) {
            if (seg.access(i) == now - 1) {
                ans.emplace_back(i - step);
                step = i;
                now--;
                break;
            }
        }
    }

    print(ans);
    return 0;
}
