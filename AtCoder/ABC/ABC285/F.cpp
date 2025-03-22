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

// すべて 0-origin
template <class T>
class FenwickTree {
public:
    const int n;
    std::vector<T> v;

    // n: 要素数
    explicit FenwickTree(const int n) : n(n), v(n + 1, 0) {}

    // v[i]
    // O(log n)
    T access(const int i) const { return this->sum(i, i + 1); }

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


// 文字列に関する関数まとめ
template <int NUM_CHARACTERS>
class StringUtility {
public:
    const int n;

private:
    std::vector<int> s;
    std::vector<FenwickTree<int>> char_ft; // 各文字

public:
    explicit StringUtility(const std::vector<int>& v) : n((int)v.size()), s(v) {
        for (int i = 0; i < NUM_CHARACTERS; ++i) {
            this->char_ft.emplace_back(n);
        }

        for (int i = 0; i < int(v.size()); ++i) {
            this->char_ft[v[i]].add(i, 1);
        }
    }

    // s[i]
    int get(const int i) const { return this->s[i]; }

    // s[i] = c
    void update(int i, int c) {
        assert(0 <= i and i < this->n);
        assert(0 <= c and c < NUM_CHARACTERS);
        // 元の文字を消す
        this->char_ft[this->s[i]].update(i, 0);

        // s[i] を c に変更する
        this->char_ft[c].add(i, 1);
        this->s[i] = c;
    }

    // 区間 [l, r) に文字 c が存在するか
    int exist(const int l, const int r, const int c) const { return this->char_ft[c].sum(l, r) > 0; }

    // 区間 [l, r) にある 文字 c の個数を求める
    int count(const int l, const int r, const int c) const {
        assert(0 <= c and c < NUM_CHARACTERS);
        return this->char_ft[c].sum(l, r);
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, Q;
    string S;
    cin >> N;
    cin >> S;
    cin >> Q;

    vector<int> T(N);
    FOR(i, 0, N) {
        T[i] = S[i] - 'a';
    }
    T.emplace_back(27);

    FenwickTree<int> ft(N);
    StringUtility<32> su(T);
    FOR(i, 0, N - 1) {
        if (T[i] <= T[i + 1]) {
            ft.update(i, 1);
        }
    }
    ft.update(N - 1, 1);

    vector<string> ans;
    FOR(_, 0, Q) {
        int T;
        cin >> T;
        if (T == 1) {
            int X;
            char C;
            cin >> X >> C;
            X--;

            su.update(X, C - 'a');
            FOR(i, max(0, X - 1), X + 1) {
                if (su.get(i) <= su.get(i + 1)) {
                    ft.update(i, 1);
                }
                else {
                    ft.update(i, 0);
                }
            }
        }
        else if (T == 2) {
            int L, R;
            cin >> L >> R;
            L--;

            if (ft.sum(L, R - 1) != R - 1 - L) {
                ans.emplace_back("No");
                continue;
            }

            int b = su.get(L);
            int e = su.get(R - 1);

            bool ok = true;
            FOR(c, b + 1, e) {
                ok &= su.count(L, R, c) == su.count(0, N, c);
            }
            if (ok) {
                ans.emplace_back("Yes");
            }
            else {
                ans.emplace_back("No");
            }
        }
    }
    print(ans);

    return 0;
}
