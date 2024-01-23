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

#include <cassert>
#include <vector>

// 各頂点がちょうど 1 の出自数をもつ有向グラフ
// グラフは連結とは限らない
template<typename T>
class FunctionalGraph {
public:
    const int num_nodes;
    std::vector<int> to;          // to[u] = u の行き先
    std::vector<bool> in_cycle;   // in_cycle[u] = u がサイクルに含まれる
    std::vector<T> value;         // 各ノードの値
    std::vector<int> color;       // 各ノードの所属コンポーネント番号
    int num_component = 0;        // グラフの個数
    std::vector<int> cycle_size;  // コンポーネントごとのサイクルのサイズ
    std::vector<T> cycle_sum;     // コンポーネントごとのサイクルの値の合計

    FunctionalGraph(const int num_nodes) : num_nodes(num_nodes) {
        this->to.resize(num_nodes, -1);
        this->in_cycle.resize(num_nodes, false);
        this->value.resize(num_nodes, 0);
        this->color.resize(num_nodes, -1);
    }

    // u -> v
    void add_directed_edge(const int u, const int v) {
        this->to[u] = v;
    }

    void set_value(const int u, const int x) {
        this->value[u] = x;
    }

    void build() {
        {
            int c = 0;
            std::vector<bool> seen(this->num_nodes, false);
            for (int u = 0; u < this->num_nodes; ++u) {
                if (color[u] == -1) {
                    this->dfs(u, c++, seen);
                }
            }
            this->num_component = c;
            this->cycle_size.resize(c);
            this->cycle_sum.resize(c);
        }

        std::vector<bool> used(this->num_nodes, false);
        for (int u = 0; u < this->num_nodes; ++u) {
            // サイクルをみつけたら，そこから到達できるノードに印をつける
            if (this->in_cycle[u] and not used[u]) {
                int c = this->color[u];
                used[u] = true;
                this->cycle_sum[c] += this->value[u];
                this->cycle_size[c]++;

                int v = this->to[u];
                while (v != u) {
                    used[v] = true;
                    this->cycle_sum[c] += this->value[v];
                    this->cycle_size[c]++;

                    this->in_cycle[v] = true;
                    v = this->to[v];
                }
            }
        }
    }

private:
    int dfs(const int u, const int c, std::vector<bool> &seen) {

        if (this->color[u] != -1) {
            return this->color[u];
        }

        // 自己ループ
        if (this->to[u] == u) {
            this->in_cycle[u] = true;
            return this->color[u] = c;
        }

        // ループ
        if (seen[u]) {
            this->in_cycle[u] = true;
            return this->color[u] = c;
        }

        seen[u] = true;
        return this->color[u] = this->dfs(this->to[u], c, seen);
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;

    FunctionalGraph<int> fg(N);
    FOR(i, 0, N) {
        int A;
        cin >> A;
        A--;
        fg.add_directed_edge(i, A);
    }
    fg.build();


    int ans = 0;
    FOR(i, 0, N) {
        ans += fg.in_cycle[i];
    }
    print(ans);


    return 0;
}