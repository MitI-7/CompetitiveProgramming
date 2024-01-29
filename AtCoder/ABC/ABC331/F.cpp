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
// 2次元配列上での移動．右，下，左，上，右上，右下，左下，左上
const std::vector<int> dy8 = {0, 1, 0, -1, -1, 1, 1, -1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};
// @formatter:on

using namespace std;

//#include <cassert>
//#include <functional>
//#include <vector>


template<class S, S (*op)(S, S), S (*unit)()>
class SegmentTree {
    const int array_size;       // もとの配列のサイズ
    int n;                      // セグ木で使う配列のサイズ
    std::vector<S> data;

public:
    SegmentTree(int array_size) : array_size(array_size) {
        this->n = 1;
        while (this->n < array_size) {
            this->n *= 2;    // array_size以上の最小の2冪
        }
        this->data.resize(2 * this->n - 1, unit());
    }

    S access(int idx) const {
        return this->data[idx + this->n - 1];
    }

    // array[idx] = x
    // O(log N)
    void update(int idx, const S x) {
        assert(0 <= idx and idx < this->array_size);
        idx += this->n - 1;   // 木での対象のインデックス
        this->data[idx] = x;
        while (idx > 0) {
            idx = (idx - 1) / 2;                                    // 親のインデックス
            this->data[idx] = op(this->data[idx * 2 + 1], this->data[idx * 2 + 2]);   // 左の子と右の子
        }
    }

    // op(array[left, right))
    // O(log N)
    S query(const int left, const int right) const {
        assert(0 <= left and left < right and right <= this->array_size);
        return query(left, right, 0, 0, this->n);
    }

private:
    // [a, b)の目的値をノードk（区間[l, r]）から検索
    S query(int a, int b, int k, int l, int r) const {
        assert(a < b && l < r);
        // 範囲外
        if (r <= a || b <= l) {
            return unit();
        }
        // 完全に含む
        if (a <= l && r <= b) {
            return this->data[k];
        }
            // 一部含む
        else {
            S vl = query(a, b, k * 2 + 1, l, (l + r) / 2);    // 左の子
            S vr = query(a, b, k * 2 + 2, (l + r) / 2, r);    // 右の子
            return op(vl, vr);
        }
    }
};


const int P = 998244353;

// Rolling Hash query
tuple<long long, long long, int> rh_op(tuple<long long, long long, int> a, tuple<long long, long long, int> b) {
    auto [h0, x0, p0] = a;
    auto [h1, x1, p1] = b;
    return {(h0 + h1 * x0) % p0, (x0 * x1) % p0, p0};
}

tuple<long long, long long, int> rh_unit() {
    return {(long long) 0, (long long) 1, P};
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, Q;
    cin >> N >> Q;
    string S;
    cin >> S;

    LL x = 121380733;

    SegmentTree<tuple<long long, long long, int>, rh_op, rh_unit> st1(N), st2(N);
    FOR(i, 0, N) {
        st1.update(i, {S[i] - 'a', x, P});
        st2.update(i, {S[N - 1 - i] - 'a', x, P});
    }

    for (int i = 0; i < Q; ++i) {
        int T;
        cin >> T;
        if (T == 1) {
            int X;
            char C;
            cin >> X >> C;
            X--;
            C -= 'a';
            st1.update(X, {C, x, P});
            st2.update(N - 1 - X, {C, x, P});
        } else {
            int L, R;
            cin >> L >> R;
            L--;
            R--;
            auto [h0, x0, p0] = st1.query(L, R + 1);
            auto [h1, x1, p1] = st2.query(N - (R + 1), N - L);
            if (h0 == h1) {
                print("Yes");
            } else {
                print("No");
            }
        }
    }

    return 0;
}