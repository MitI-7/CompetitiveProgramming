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

class Range {
public:
    const int n;
    std::set<int> s;

    Range(const int n) : n(n) {
        this->s.insert(-1);
        this->s.insert(n);
    }

    void insert(const int i) {
        assert(0 <= i and i < this->n);
        this->s.insert(i);
    }

    int head(const int i) const {
        assert(0 <= i and i < this->n);
        auto it = this->s.upper_bound(i);
        --it;
        return *it;
    }

    std::pair<int, int> range(const int i) const {
        assert(0 <= i and i < this->n);
        const int head = this->head(i);
        const int next_head = this->next_head(i);
        return {head, next_head};
    }

    int prev_head(const int i) const {
        assert(0 <= i and i < this->n);
        auto it = this->s.lower_bound(i);
        --it;
        return *it;
    }

    int next_head(const int i) const {
        assert(0 <= i and i < this->n);
        return *this->s.upper_bound(i);
    }

    void erase_head(const int i) {
        assert(0 <= i and i < this->n);
        this->s.erase(this->head(i));
    }

    void dump() const {
        for (const auto head : this->s) {
            std::cout << head << " ";
        }
        std::cout << std::endl;
    }
};

using namespace std;

vector<int> solve(const int N, const vector<tuple<int, int, int>> &queries) {
    Range range(N);
    map<int, int> color_num;
    map<int, int> head_color;
    FOR(i, 0, N) {
        range.insert(i);
        color_num[i] = 1;
        head_color[i] = i;
    }
    head_color[-1] = -1;
    head_color[N] = -2;

    vector<int> ans;
    for (auto [T, X, C] : queries) {
        if (T == 1) {
            const auto head = range.head(X);
            const int now_color = head_color[head];
            if (now_color == C) {
                continue;
            }

            const auto [l, r] = range.range(head);
            color_num[now_color] -= r - l;
            color_num[C] += r - l;
            head_color[head] = C;

            // 左と結合
            const int prev_head = range.prev_head(head);
            if (head_color[prev_head] == C and prev_head != -1) {
                range.erase_head(head);
            }

            // 右と結合
            const int next_head = range.next_head(head);
            if (head_color[next_head] == C and next_head != N) {
                range.erase_head(next_head);
            }
        }
        else {
            ans.emplace_back(color_num[C]);
        }
    }
    return ans;
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, Q;
    cin >> N >> Q;

    vector<tuple<int, int, int>> queries;
    for (int i = 0; i < Q; ++i) {
        int T, X, C;
        cin >> T;
        if (T == 1) {
            cin >> X >> C;
            X--;
            C--;
            queries.emplace_back(T, X, C);
        }
        else {
            cin >> C;
            C--;
            queries.emplace_back(T, 0, C);
        }
    }

    auto ans = solve(N, queries);
    print(ans);

    return 0;
}
