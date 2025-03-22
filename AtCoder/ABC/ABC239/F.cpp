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

// #include <numeric>
// #include <set>
// #include <vector>

class UnionFind {
public:
    const int num_nodes; // 要素の個数
    int set_size; // 集合の個数
    std::set<int> leaders;

private:
    std::vector<int> parent; // 親の番号(親だった場合は-(その集合のサイズ))
    std::vector<int> next;

public:
    explicit UnionFind(const int num_nodes) : num_nodes(num_nodes), set_size(num_nodes), parent(num_nodes, -1) {
        this->next.resize(num_nodes);
        std::iota(this->next.begin(), this->next.end(), 0);
        for (int u = 0; u < num_nodes; ++u) {
            this->leaders.insert(u);
        }
    }

    // u と v が同じ集合に属するか判定する
    bool is_same_set(const int u, const int v) { return this->find_root(u) == this->find_root(v); }

    // u と v の属する集合を併合する
    bool unite(int u, int v) {
        u = this->find_root(u);
        v = this->find_root(v);
        if (u == v) {
            return false;
        }

        // 集合のサイズが大きい方を u とする
        if (this->parent[u] > this->parent[v]) {
            std::swap(u, v);
        }

        // u の下に v をつける
        this->parent[u] += this->parent[v];
        this->parent[v] = u;
        std::swap(this->next[v], this->next[u]);
        this->set_size--;
        this->leaders.erase(v);

        return true;
    }

    // u の属する集合の要素数を求める
    int size(const int u) { return (-this->parent[this->find_root(u)]); }

    int leader(const int u) { return this->find_root(u); }

    // u の所属する集合のメンバーを求める
    // O(メンバーの人数)
    std::vector<int> group(const int u) {
        std::vector<int> group(this->size(u));
        int now = this->find_root(u);
        for (int i = 0; i < static_cast<int>(group.size()); ++i) {
            group[i] = now = this->next[now];
        }
        return group;
    }

private:
    // 木の根を求める
    int find_root(const int u) {
        if (this->parent[u] < 0) {
            return u;
        } else {
            return this->parent[u] = this->find_root(this->parent[u]);
        }
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, M;
    cin >> N >> M;
    vector<int> D(N);
    FOR(i, 0, N) { cin >> D[i]; }

    UnionFind uf(N);
    FOR(i, 0, M) {
        int U, V;
        cin >> U >> V;
        U--;
        V--;

        if (uf.is_same_set(U, V)) {
            print(-1);
            return 0;
        }

        uf.unite(U, V);
        D[U]--;
        D[V]--;

        if (D[U] < 0 or D[V] < 0) {
            print(-1);
            return 0;
        }
    }

    MaxPriorityQueue<tuple<int, vector<int>>> que;
    FOE(l, uf.leaders) {
        vector<int> m;
        int n = 0;
        FOE(u, uf.group(l)) {
            if (D[u] > 0) {
                m.emplace_back(u);
                n += D[u];
            }
        }
        if (n > 0) {
            que.emplace(n, m);
        }
    }

    vector<pair<int, int>> ans;
    while (LEN(que) >= 2) {
        auto [n1, m1] = que.top();
        que.pop();
        auto [n2, m2] = que.top();
        que.pop();

        const int n = n1 + n2 - 2;
        ans.emplace_back(m1.back() + 1, m2.back() + 1);
        D[m1.back()]--;
        D[m2.back()]--;
        if (D[m1.back()] == 0) {
            m1.pop_back();
        }
        if (D[m2.back()] == 0) {
            m2.pop_back();
        }

        if (LEN(m2) > LEN(m1)) {
            swap(m1, m2);
        }
        FOE(u, m2) { m1.emplace_back(u); }

        if (n > 0) {
            que.emplace(n, m1);
        }
    }

    if (LEN(ans) == N - M - 1 and reduce(ALL(D)) == 0) {
        FOE(p, ans) { print(p); }
    } else {
        print(-1);
    }

    return 0;
}
