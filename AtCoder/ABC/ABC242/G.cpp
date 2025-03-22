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

// #include <algorithm>
// #include <cmath>
// #include <vector>

// 1 回の伸縮の計算量が a のとき O(a * N * sqrt(Q))
template<class T, T (*add)(int, T), T (*del)(int, T)>
class Mo {
    struct Query {
        int id;
        int left;
        int right;
    };

public:
    const int num_query; // クエリの数
    std::vector<Query> queries; // クエリ
    const int num_bucket; // バケットの数

private:
    int now_left = 0, now_right = 0; // 現在見ている区間[now_left, now_right)

public:
    // n: 配列の長さ
    // num_query: クエリの個数
    // bucket = sqrt(3) * N / sqrt(2 * Q)
    Mo(const int n, const int num_query) :
        num_query(num_query), queries(num_query),
        num_bucket(std::max<int>(1, (double) n / std::max<double>(1.0, sqrt(num_query * 2.0 / 3.0)))) {}

    // [l, r)
    void add_query(const int id, const int l, const int r) {
        this->queries[id].id = id;
        this->queries[id].left = l;
        this->queries[id].right = r;
    }

    std::vector<T> solve() {
        this->sort_queries();

        std::vector<T> ans(this->num_query);

        T now_ans = 0;
        for (const auto [id, left, right]: this->queries) {

            // [now_left, now_right) を queryの [left, right) になるように調整
            // now_left を左にずらす
            while (left < this->now_left) {
                now_ans = add(--this->now_left, now_ans);
            }
            // now_right を右にずらす
            while (this->now_right < right) {
                now_ans = add(this->now_right++, now_ans);
            }
            // now_left を右にずらす
            while (this->now_left < left) {
                now_ans = del(this->now_left++, now_ans);
            }
            // now_right を左にずらす
            while (this->now_right > right) {
                now_ans = del(--this->now_right, now_ans);
            }

            ans[id] = now_ans;
        }

        return ans;
    }

private:
    // クエリをソートする
    void sort_queries() {
        std::sort(this->queries.begin(), this->queries.end(), [&](const Query &l, const Query &r) -> bool {
            const unsigned int left_bucket = l.left / this->num_bucket; // クエリ l の所属するバケット
            const unsigned int right_bucket = r.left / this->num_bucket; // クエリ r の所属するバケット

            // クエリ [L, R) の L の所属するバケットが違うなら，L の所属するバケットで比較
            if (left_bucket != right_bucket) {
                return left_bucket < right_bucket;
            } else {
                // 定数倍高速化
                // 奇数番目のバケットだけ右のソート順を逆にして，バケットを移動したときの now_right
                // を移動する距離を短くする
                if (left_bucket & 1u) {
                    return l.right < r.right;
                } else {
                    return l.right > r.right;
                }
            }
        });
    }
};


// 問題特有のデータ
std::vector<int> A;
vector<int> c;

// A[idx] が追加されたときの状態の変化と答えを計算
template<class T>
T add(const int idx, T query_ans) {
    c[A[idx]]++;
    T diff = c[A[idx]] % 2 == 0;
    return query_ans + diff;
}

// A[idx] が削除されたときの状態の変化と答えを計算
template<class T>
T del(const int idx, T query_ans) {
    T diff = c[A[idx]] % 2 == 0;
    c[A[idx]]--;

    return query_ans - diff;
}


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N;
    cin >> N;
    A.resize(N);
    c.resize(N);
    FOR(i, 0, N) {
        cin >> A[i];
        A[i]--;
    }

    int Q;
    cin >> Q;
    Mo<int, add, del> mo(N, Q);
    FOR(i, 0, Q) {
        int L, R;
        cin >> L >> R;
        L--;
        R--;
        mo.add_query(i, L, R + 1);
    }

    auto ans = mo.solve();
    print(ans);

    return 0;
}
