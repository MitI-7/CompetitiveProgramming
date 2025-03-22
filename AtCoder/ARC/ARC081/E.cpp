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

// a の区間 [l, r) に出現するある整数値 x の個数をカウントするクエリに答える
template<typename T>
class StaticRangeFrequency {
public:
    int n;

private:
    std::vector<T> a;
    std::unordered_map<T, std::vector<int>> idx_list; // 各値の出現する index

public:
    explicit StaticRangeFrequency(const std::vector<T> &a) : n(static_cast<int>(a.size())), a(a) {
        for (int i = 0; i < static_cast<int>(a.size()); ++i) {
            this->idx_list[a[i]].emplace_back(i);
        }
    }

    // a[i]
    T access(const int i) const { return this->a[i]; }

    void emplace_back(const int x) {
        this->a.emplace_back(x);
        this->idx_list.at(x).emplace_back(this->n);
        ++this->n;
    }

    // x の個数を求める
    // O(1)
    int count(const T x) const {
        if (not this->idx_list.contains(x)) {
            return 0;
        }
        return static_cast<int>(this->idx_list.at(x).size());
    }

    // 区間[l, r) に存在する x の個数を求める
    // O(log n)
    int count_range(const T x, const int l, const int r) const {
        if (this->count(x) == 0) {
            return 0;
        }

        const auto begin = this->idx_list.at(x).begin();
        const auto end = this->idx_list.at(x).end();
        const auto it_left = std::lower_bound(begin, end, l);
        if (it_left == end) {
            return 0;
        }

        const auto it_right = std::lower_bound(begin, end, r);
        return static_cast<int>(std::distance(it_left, it_right));
    }

    // 位置 l 以降に最初にでてくる x の位置を求める(lを含む)
    // ない場合は n を返す
    int next(const T x, const int l) {
        if (not this->idx_list.contains(x)) {
            return this->n;
        }

        auto it = std::lower_bound(this->idx_list.at(x).begin(), this->idx_list.at(x).end(), l);
        if (it != this->idx_list.at(x).end()) {
            return *it;
        }

        return this->n;
    }

    // 位置 r 以前に最初にでてくる x の位置を求める(rを含む)
    // ない場合は -1 を返す
    int prev(const T x, const int r) {
        if (not this->idx_list.contains(x)) {
            return -1;
        }

        auto it = std::lower_bound(this->idx_list.at(x).begin(), this->idx_list.at(x).end(), r);
        if (it != this->idx_list.at(x).end() and *it == r) {
            return r;
        }

        if (it != this->idx_list.at(x).begin()) {
            --it;
            return *it;
        }

        return -1;
    }

    // 区間[l, r) で k 番目にでてくる x の index
    // k は 0-index．ない場合は -1 を返す
    int kth_x(const T x, const int k, const int l, const int r) const {
        assert(0 <= l and r <= this->n and l <= r);
        if (not this->idx_list.contains(x)) {
            return -1;
        }

        const auto it = lower_bound(this->idx_list.at(x).begin(), this->idx_list.at(x).end(), l);
        if (it == this->idx_list.at(x).end()) {
            return -1;
        }

        // l 以降にでてくる最初の x の index
        const int idx = distance(this->idx_list.at(x).begin(), it);
        if (idx + k < static_cast<int>(this->idx_list.at(x).size())) {
            if (this->idx_list.at(x)[idx + k] < r) {
                return this->idx_list.at(x)[idx + k];
            }
        }
        return -1;
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    string A;
    cin >> A;
    const int N = LEN(A);

    vector<int> v(N + 1);
    v[0] = 30;
    FOR(i, 0, N) { v[i + 1] = A[i] - 'a'; }

    StaticRangeFrequency srf(v);
    auto dp = make_v<int>(N + 2);
    fill_v(dp, INF);

    dp[N + 1] = 0;
    for (int i = N; i >= 0; --i) {
        FOR(c, 0, 26) {
            const int j = srf.next(c, i + 1);
            chmin(dp[i], dp[j] + 1);
        }
    }

    string ans;
    int now = 0;
    while (now < N) {
        FOR(c, 0, 26) {
            const int j = srf.next(c, now + 1);
            if (dp[j] == dp[now] - 1) {
                ans.push_back(c + 'a');
                now = j;
                break;
            }
        }
    }
    print(ans);

    return 0;
}
