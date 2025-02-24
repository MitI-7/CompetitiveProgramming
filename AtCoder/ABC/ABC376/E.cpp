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

template<typename T>
class TopK {
private:
    T top_k_sum = 0;// 上位 k 件の合計
    int k;
    const bool reverse;      // 小さい順にする
    std::multiset<T> top_k;  // 上位 k 件
    std::multiset<T> reserve;// 補欠

public:
    // reverse = false の場合，大きい順に k 件を管理．trueの場合，小さい順に k 件を管理する
    explicit TopK(const int k, const bool reverse = false) : k(k), reverse(reverse) {
        assert(k >= 0);
    }

    // 現在の要素数を求める
    [[nodiscard]] int size() const {
        return this->top_k.size() + this->reserve.size();
    }

    // k を変更する
    // O(abs(new_k - k))
    void change_k(const int new_k) {
        assert(new_k >= 0);

        if (new_k == this->k) {
            return;
        }

        this->k = new_k;
        this->balance();
    }

    // 上位 k 件の合計を求める
    // O(1)
    [[nodiscard]] T get_top_k_sum() {
        if (this->reverse) {
            return this->top_k_sum * -1;
        }
        return this->top_k_sum;
    }

    // 1 番目の値を求める
    [[nodiscard]] T get_top() {
        assert(this->size() > 0);
        if (this->reverse) {
            return *this->top_k.rbegin() * -1;
        }
        return *this->top_k.rbegin();
    }

    // k 番目の値を求める
    [[nodiscard]] T get_top_k() {
        assert(this->size() > 0);
        if (this->reverse) {
            return *this->top_k.begin() * -1;
        }
        return *this->top_k.begin();
    }

    // O(log n)
    void insert(T x) {
        if (this->reverse) {
            x *= -1;
        }
        this->top_k.insert(x);
        this->top_k_sum += x;
        this->balance();
    }

    // O(log n)
    void erase(T x) {
        if (this->reverse) {
            x *= -1;
        }

        // 補欠にいるなら，補欠から削除するだけ
        {
            const auto it = this->reserve.find(x);
            if (it != this->reserve.end()) {
                this->reserve.erase(it);
                return;
            }
        }

        {
            const auto it = this->top_k.find(x);
            if (it != this->top_k.end()) {
                this->top_k_sum -= x;
                this->top_k.erase(it);
                this->balance();
            }
        }
    }

private:
    void balance() {
        // top k が k 個以上あるなら最小の要素を補欠に送る
        while ((int) this->top_k.size() > this->k) {
            auto mini = this->top_k.begin();
            this->top_k_sum -= *mini;
            this->reserve.insert(*mini);
            this->top_k.erase(mini);
        }

        // top k が k に満たないなら補欠から最大の要素を送る
        while ((int) this->top_k.size() < this->k and not this->reserve.empty()) {
            auto maxi = this->reserve.rbegin();
            this->top_k_sum += *maxi;
            this->top_k.insert(*maxi);
            this->reserve.erase((++maxi).base());
        }
    }
};

void solve() {
    int N, K;
    cin >> N >> K;
    vector<pair<LL, LL>> AB(N);
    FOR(i, 0, N) {
        cin >> AB[i].first;
    }
    FOR(i, 0, N) {
        cin >> AB[i].second;
    }

    sort(ALL(AB));

    TopK<LL> top_k(K, true);
    FOR(i, 0, K) {
        top_k.insert(AB[i].second);
    }

    LL ans = AB[K - 1].first * top_k.get_top_k_sum();
    FOR(i, K, N) {
        top_k.insert(AB[i].second);
        chmin(ans, AB[i].first * top_k.get_top_k_sum());
    }
    print(ans);
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int T;
    cin >> T;
    FOR(i, 0, T) {
        solve();
    }

    return 0;
}
