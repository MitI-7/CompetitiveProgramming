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

template<class T = long long>
class CoordinateCompression {
private:
    bool initialized;
    std::set<T> s;

    int no = 0;
    std::unordered_map<T, int> _zip;
    std::unordered_map<int, T> _unzip;

public:
    CoordinateCompression() : initialized(false) {}

    void add(T x) {
        this->s.insert(x);
    }

    int size() {
        if (not this->initialized) {
            this->build();
        }
        return this->no;
    }

    // 元の値 -> 圧縮した値
    int zip(const T x) {
        if (not this->initialized) {
            this->build();
        }
        return this->_zip.at(x);
    }

    // 圧縮した値 -> 元の値
    T unzip(const int i) {
        if (not this->initialized) {
            this->build();
        }
        return this->_unzip.at(i);
    }

private:
    void build() {
        this->initialized = true;
        for (auto x: this->s) {
            this->_zip[x] = this->no;
            this->_unzip[this->no] = x;
            this->no++;
        }
    }
};

template<typename T>
class CumulativeSum {
private:
    std::vector<T> memo;

public:
    CumulativeSum() {
    }

    CumulativeSum(const std::vector<T> &line) {
        this->build(line);
    }

    void build(const std::vector<T> &line) {
        this->memo = std::vector<T>(line.size() + 1, 0);
        for (int i = 0; i < int(line.size()); ++i) {
            this->memo[i + 1] = this->memo[i] + line[i];
        }
    }

    // sum[left, right)
    T sum(const int left, const int right) const {
        assert(right >= left);
        return this->memo[right] - this->memo[left];
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;

    CoordinateCompression<int> cc;
    vector<int> X(N), P(N);
    FOR(i, 0, N) {
        cin >> X[i];
        cc.add(X[i]);
    }
    FOR(i, 0, N) {
        cin >> P[i];
    }

    int Q;
    cin >> Q;
    vector<pair<int, int>> queries(Q);
    FOR(i, 0, Q) {
        int L, R;
        cin >> L >> R;
        queries[i] = {L, R};
        cc.add(L);
        cc.add(R);
    }

    vector<LL> h(cc.size());
    FOR(i, 0, N) {
        h[cc.zip(X[i])] = P[i];
    }
    CumulativeSum<LL> cs(h);

    vector<LL> ans;
    for (auto [l, r] : queries) {
        ans.emplace_back(cs.sum(cc.zip(l), cc.zip(r) + 1));
    }
    print(ans);

    return 0;
}
