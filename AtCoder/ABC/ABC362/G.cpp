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

class SuffixArray {
    int n;
    int k;
    std::vector<int> rank;

public:
    const std::string s;
    std::vector<int> sa;
    std::vector<int> lcp;

    SuffixArray(const std::string &s) : n(s.size()), s(s) {
        this->sa.resize(n + 1, 0);
        this->lcp.resize(n + 1, 0);
        this->rank.resize(n + 1, 0);
    }

    // O(n log^2 n)
    void build_suffix_array() {
        this->construct_sa();
        this->construct_lcp();
    }

    // sがpatternを含んでいるか
    // O(|pattern| log |S|)
    bool contain(const std::string &pattern) const {
        return this->contain(pattern, 0, this->n);
    }

    // s[left, right)がpatternを含んでいるか
    // O(|pattern| log |S|)
    bool contain(const std::string &pattern, int left, int right) const {
        assert(left >= 0);
        assert(right <= this->n);
        assert(left < right);

        const int pattern_size = pattern.length();
        while (right - left > 1) {
            int c = (left + right) / 2;
            // Sのsa[c]文字目から|pattern|文字をpatternを比較
            if (this->s.compare(this->sa[c], pattern_size, pattern) < 0) {
                left = c;
            } else {
                right = c;
            }
        }

        return this->s.compare(this->sa[right], pattern_size, pattern) == 0;
    }

    // pattern の出現回数(重なりを許す)
    int count(const std::string &pattern) const {
        const auto l = this->lower_bound_sa(pattern);
        const auto u = this->upper_bound_sa(pattern);
        if (l == -1 or u == -1) {
            return 0;
        }
        return u - l + 1;
    }

    // // s上で最初にpatternが出現する位置(0-index)
    // int find_first(const std::string &pattern) const {
    //     const auto l = this->lower_bound_sa(pattern);
    //     const auto u = this->upper_bound_sa(pattern);
    //     if (l == -1 or u == -1) {
    //         return -1;
    //     }
    //     return this->st.range_minimum_query(l, u + 1);
    // }
    //
    // // s上で最後にpatternが出現する位置(0-index)
    // int find_last(const std::string &pattern) const {
    //     const auto l = this->lower_bound_sa(pattern);
    //     const auto u = this->upper_bound_sa(pattern);
    //     if (l == -1 or u == -1) {
    //         return -1;
    //     }
    //     return this->st.range_maximum_query(l, u + 1);
    // }

    // sa上で最初にpatternが現れる位置
    int lower_bound_sa(const std::string &pattern) const {
        const int pattern_size = pattern.size();

        int left = -1, right = n;
        while (right - left > 1) {
            const auto m = std::midpoint(left, right);
            const int ret = this->s.compare(this->sa[m], pattern_size, pattern);
            // patternが大きい
            if (ret >= 0) {
                right = m;
            } else {
                left = m;
            }
        }
        if (this->s.compare(this->sa[right], pattern_size, pattern) == 0) {
            return right;
        }
        return -1;
    }

    // sa上で最後にpatternが現れる位置
    int upper_bound_sa(const std::string &pattern) const {
        const int pattern_size = pattern.size();

        int left = -1, right = this->n + 1;
        while (right - left > 1) {
            const auto m = std::midpoint(left, right);
            const auto ret = this->s.compare(this->sa[m], pattern_size, pattern);
            // patternが小さい
            if (ret <= 0) {
                left = m;
            } else {
                right = m;
            }
        }

        if (this->s.compare(this->sa[left], pattern_size, pattern) == 0) {
            return left;
        }
        return -1;
    }

    void debug() {
        std::cout << "idx lcp sa sa[i]" << std::endl;
        for (int i = 0; i <= n; ++i) {
            std::cout << i << " " << lcp[i] << " " << sa[i] << " " << s.substr(sa[i]) << std::endl;
        }
    }

private:
    struct compare {
        compare(const SuffixArray &sa) : sa(sa) {}

        const SuffixArray &sa;

        // (rank[i], rank[i + k])と(rank[j], rank[j + k])を比較
        bool operator()(const int &i, const int &j) const {
            if (sa.rank[i] != sa.rank[j]) {
                return sa.rank[i] < sa.rank[j];
            } else {
                const int ri = i + sa.k <= sa.n ? sa.rank[i + sa.k] : -1;
                const int rj = j + sa.k <= sa.n ? sa.rank[j + sa.k] : -1;
                return ri < rj;
            }
        }
    };

    void construct_sa() {
        std::vector<int> tmp(this->n + 1, 0);

        for (int i = 0; i <= this->n; i++) {
            this->sa[i] = i;
            this->rank[i] = i < this->n ? this->s[i] : -1;
        }
        // k文字についてソートされているところから、2k文字でソートする
        for (this->k = 1; this->k <= this->n; this->k *= 2) {
            std::sort(this->sa.begin(), this->sa.end(), compare(*this));
            // いったんtmpに次のランクを計算し、それからrankに移す
            tmp[this->sa[0]] = 0;
            for (int i = 1; i <= this->n; i++) {
                tmp[this->sa[i]] = tmp[this->sa[i - 1]] + (compare(*this).operator()(this->sa[i - 1], this->sa[i]) ? 1 : 0);
            }
            for (int i = 0; i <= this->n; i++) {
                this->rank[i] = tmp[i];
            }
        }
    }

    void construct_lcp() {
        for (int i = 0; i <= this->n; i++) {
            this->rank[this->sa[i]] = i;
        }
        int h = 0;
        this->lcp[0] = 0;
        for (int i = 0; i < this->n; i++) {
            // 文字列中での位置iの接尾辞と、接尾辞配列中でその1つ前の接尾辞のLCPを求める
            int j = this->sa[this->rank[i] - 1];
            // hを先頭の分1減らし、後ろが一致しているだけ増やす
            if (h > 0) {
                h--;
            }
            for (; j + h < this->n and i + h < this->n; h++) {
                if (this->s[j + h] != this->s[i + h]) {
                    break;
                }
            }
            this->lcp[this->rank[i] - 1] = h;
        }
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    string S;
    cin >> S;

    SuffixArray sa(S);
    sa.build_suffix_array();

    int Q;
    cin >> Q;
    vector<int> ans(Q);
    for (int i = 0; i < Q; i++) {
        string T;
        cin >> T;
        ans[i] = sa.count(T);
    }
    print(ans);

    return 0;
}
