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
        // y == x
        if (*i == x) {
            return distance(a.begin(), i);
        }
        else {
            return distance(a.begin(), i) - 1;
        }
    }

    // [l, r)のx以下の個数
    int count_lte(const std::vector<T> &a, T x, int l, int r) {
        if (l == r) {
            return 0;
        }
        assert(l < r);
        assert(0 <= l);
        assert(r <= a.size());
        return upper_bound(a.begin() + l, a.begin() + r, x) - (a.begin() + l);
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

LL solve(int N, LL K, vector<LL> A) {
    auto pos = make_v<LL>(0);
    auto neg = make_v<LL>(0);

    FOR(i, 0, N) {
        if (A[i] > 0) {
            pos.emplace_back(A[i]);
        }
        else if (A[i] < 0) {
            neg.emplace_back(-A[i]);
        }
    }

    LL num_pos = LEN(pos);
    LL num_neg = LEN(neg);
    LL num_zero = N - num_pos - num_neg;

    sort(ALL(neg));
    sort(ALL(pos));

    BisectWrapper<LL> bw;
    if (K <= num_neg * num_pos) {
        LL left = -LINF;
        LL right = 0;
        while (right - left > 1) {
            LL c = (right + left) / 2;
            LL num = 0;
            FOR(i, 0, num_neg) {
                num += bw.count_gte(pos, ceil(-c, neg[i]));
            }

            if (num >= K) {
                right = c;
            }
            else {
                left = c;
            }
        }

        return right;
    }

    K -= num_neg * num_pos;
    if (K <= num_zero * (num_pos + num_neg) + (num_zero * (num_zero - 1) / 2)) {
        return 0;
    }

    K -= num_zero * (num_pos + num_neg) + (num_zero * (num_zero - 1) / 2);
    LL left = 0;
    LL right = LINF;

    while ((right - left) > 1) {
        LL c = (right + left) / 2;

        LL num = 0;
        FOR(i, 0, num_neg) {
            num += bw.count_lte(neg, c / neg[i], i + 1, num_neg);
        }
        FOR(i, 0, num_pos) {
            num += bw.count_lte(pos, c / pos[i], i + 1, num_pos);
        }

        if (num >= K) {
            right = c;
        }
        else {
            left = c;
        }
    }

    return right;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    LL N, K;
    cin >> N >> K;
    auto A = make_v<LL>(N);
    FOR(i, 0, N) {
        cin >> A[i];
    }

    print(solve(N, K, A));

    return 0;
}