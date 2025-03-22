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
// #include <vector>

template<typename T>
class Doubling {
    const int LOG;
    std::vector<std::vector<T>> table; // table[k][i] = iのk回遷移先の値
    bool initialized;

public:
    // n: function(x) の x の最大値
    // max_k: function 関数を適用する回数 k の最大値
    Doubling(int n, long long max_k) : LOG(64 - __builtin_clzll(max_k)), initialized(false) {
        this->table.assign(LOG, std::vector<T>(n, -1));
    }

    // xの遷移先
    // function(x) = y
    void function(const int x, const T y) {
        assert(not this->initialized);
        this->table[0][x] = y;
    }

    // a に function 関数を k 回適用したときの値
    // O(log k)
    T query(T a, unsigned long long k) {
        if (not this->initialized) {
            this->build();
        }
        for (int i = this->LOG - 1; i >= 0; i--) {
            if ((k >> i) & 1) {
                a = this->table[i][a];
            }
        }

        return a;
    }

private:
    // O(N log max_k)
    void build() {
        for (int k = 0; k + 1 < this->LOG; ++k) {
            for (int i = 0; i < int(this->table[k].size()); ++i) {
                if (this->table[k][i] == -1) {
                    this->table[k + 1][i] = -1;
                } else {
                    this->table[k + 1][i] = this->table[k][this->table[k][i]];
                }
            }
        }
        this->initialized = true;
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;
    vector<int> X(N);
    FOR(i, 0, N) {
        cin >> X[i];
    }
    int L;
    cin >> L;

    vector v = {Doubling<LL>(N, 1000000100), Doubling<LL>(N, 1000000100)};
    FOR(i, 0, 2) {
        int r = 0;
        FOR(l, 0, N) {
            while (r < N and abs(X[l] - X[r]) <= L) {
                ++r;
            }
            v[i].function(l, r - 1);
        }
        reverse(ALL(X));
    }

    int Q;
    cin >> Q;
    vector<int> ans(Q);
    FOR(i, 0, Q) {
        int A, B;
        cin >> A >> B;
        A--;
        B--;

        if (A < B) {
            int left = 0, right = INF;
            while (right - left > 1) {
                const auto mid = std::midpoint(left, right);
                if (v[0].query(A, mid) >= B) {
                    right = mid;
                } else {
                    left = mid;
                }
            }
            ans[i] = right;
        } else {
            A = N - A - 1;
            B = N - B - 1;
            int left = 0, right = INF;
            while (right - left > 1) {
                const auto mid = std::midpoint(left, right);
                if (v[1].query(A, mid) >= B) {
                    right = mid;
                } else {
                    left = mid;
                }
            }
            ans[i] = right;
        }
    }
    print(ans);

    return 0;
}
