#include <bits/stdc++.h>

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for(int i=(a);i<(n); ++i)
#define FOE(i, a) for(auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define BIT_COUNT32(bit) (__builtin_popcount(bit))
#define BIT_COUNT64(bit) (__builtin_popcountll(bit))

// @formatter:off
typedef long long LL;
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
template<class T> inline T manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }
template<typename T> T &chmin(T &a, const T &b) { return a = std::min(a, b); }
template<typename T> T &chmax(T &a, const T &b) { return a = std::max(a, b); }
bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }
unsigned long long get_bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) { assert(b == 0 or b == 1); if (b == 0) { return bit & ~(1ull << i); } else {return bit | (1ull << i);}}

// 初項s交差d長さnの数列の和
long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}

// 三角数
long long triangular_number(long long n) {
    return n * (n + 1) / 2;
}

// sqrt(x)の整数解を求める
// 整数解がなければ-1
long long sqrt_integer(const long long x) {
    if (x < 0) {
        return -1;
    }
    auto a = (long long)sqrt(x);
    if (a * a == x) {
        return a;
    }
    if((a - 1) * (a - 1) == x) {
        return a - 1;
    }
    if((a + 1) * (a + 1) == x) {
        return a + 1;
    }

    return -1;
}

// xが2の階乗かどうか判定
bool is_power_of_two(long long x) {
    return !(x & (x - 1));
}

// O(log max(a, b))
long long gcd(long long a, long long b) {
    if (b == 0) { return a; }
    return gcd(b, a % b);
}

long long lcm(long long a, long long b) {
    long long g = gcd(a, b);
    return a / g * b;
}

const int INF = 1u << 30u;  // 1,073,741,824
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
// 2次元配列上での移動
const std::vector<int> dy2 = {0, 1}, dx2 = {1, 0};  // 右，下
const std::vector<int> dy4 = {0, 1, 0, -1}, dx4 = {1, 0, -1, 0};    // 右，下，左，上
const std::vector<int> dy6 = {0, -1, 0, 1, 1, 1}, dx6 = {1, 0, -1, 0, 1, -1};
const std::vector<int> dy8 = {0, -1, 0, 1, 1, -1, -1, 1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};
// @formatter:on

using namespace std;

#include <algorithm>
#include <cassert>
#include <vector>

template<class T>
class SortedVectorUtility {
private:
    std::vector<T> a;
public:
    explicit SortedVectorUtility(std::vector<T> &a) : a(a) {}

    // xが存在するか
    bool exist(T x) const {
        return binary_search(a.begin(), a.end(), x);
    }

    // xの個数
    int count(const T x) const {

    }

    // x 以下の要素の個数
    int count_equal_less_than(const T x) const {
        return std::upper_bound(a.begin(), a.end(), x) - a.begin();
    }

    // x より小さい要素の個数
    int count_lt(const T x) const {
        return std::lower_bound(a.begin(), a.end(), x) - a.begin();
    }

    // x 以上の要素の個数
    int count_gte(T x) const {
        return a.end() - std::lower_bound(a.begin(), a.end(), x);
    }

    // x より大きい要素の個数
    int count_gt(const T x) const {
        return a.size() - this->count_elt(a, x);
    }

    // x以上y未満の要素の個数
    int count_range(T x, T y) {
        return this->count_lt(y) - this->count_lt(x);
    }

    // 区間[l, r)に存在する x 以下の個数
    int count_lte_range(int l, int r, T x) const {
        if (l == r) {
            return 0;
        }
        assert(l < r);
        assert(0 <= l);
        assert(r <= int(a.size()));
        return upper_bound(a.begin() + l, a.begin() + r, x) - (a.begin() + l);
    }

    // 区間[l, r)に存在する x 以上の個数
    int count_gte_range(int l, int r, T x) const {
        if (l == r) {
            return 0;
        }
        assert(l < r);
        assert(0 <= l);
        assert(r <= int(a.size()));
        return (a.begin() + r) - std::lower_bound(a.begin() + l, a.begin() + r, x);
    }

    // x の index
    // 複数ある場合一番小さい値
    // なければ -1
    int index(const T x) const {
        auto i = lower_bound(a.begin(), a.end(), x);
        if (i != a.end() and a[i] == x) {
            return distance(a.begin(), i);
        }
    }

    // x 以下で最大の値のインデックス
    int index_predecessor(const T x) const {
        auto it = std::upper_bound(a.begin(), a.end(), x);
        if (it == a.begin()) {
            return -1;
        }
        --it;
        return distance(it, a.begin());
    }

    // x 以上の値の中で最小の値のインデックス
    // ない場合は -1 を返す
    int index_successor(const T x) const {
        auto it = std::lower_bound(a.begin(), a.end(), x);
        if (it == a.end()) {
            return -1;
        }
        return distance(a.begin(), it);
    }

    // y < xのようなyの中でもっとも大きいindex
    // ない場合は -1 を返す
    int index_lt(const T x) const {
        auto i = lower_bound(a.begin(), a.end(), x);
        return distance(a.begin(), i) - 1;
    }

    // y <= xのようなyの中でもっとも大きいindex
    int index_lte(const T x) const {
        auto i = lower_bound(a.begin(), a.end(), x);
        // y == x
        if (*i == x) {
            return distance(a.begin(), i);
        }
        else {
            return distance(a.begin(), i) - 1;
        }
    }

    // y > xのようなyの中でもっとも小さいのindex
    // なければN
    int index_gt(const T x) const {
        auto i = upper_bound(a.begin(), a.end(), x);
        return distance(a.begin(), i);
    }

    // y >= xのようなyの中でもっとも小さいのindex
    int index_gte(const T x) const {
        auto i = lower_bound(a.begin(), a.end(), x);
        return distance(a.begin(), i);
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;
    vector<LL> A(N);
    FOR(i, 0, N) {
        cin >> A[i];
    }

    vector<LL> cs(N);
    FOR(i, 1, N) {
        cs[i] += cs[i - 1];
        // 起きた
        if (i % 2 == 0) {
            cs[i] += A[i] - A[i - 1];
        }
    }

    SortedVectorUtility<LL> svu(A);

    auto f = [&](LL X) {
        int i = svu.index_lte(X);
        if (i == -1) {
            return (LL) 0;
        }

        LL ans = cs[i];
        if (i % 2 != 0) {
            ans += (X - A[i]);
        }

        return ans;
    };

    int Q;
    cin >> Q;
    vector<LL> ans(Q);
    FOR(i, 0, Q) {
        LL L, R;
        cin >> L >> R;
        ans[i] = f(R) - f(L);
    }
    print(ans);

    return 0;
}