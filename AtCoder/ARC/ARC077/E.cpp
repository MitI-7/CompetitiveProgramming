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

template<typename T>
class ImosArithmeticSequence {
public:
    const int N;

    // private:
    std::vector<T> line;

public:
    ImosArithmeticSequence(int N) : N(N), line(N + 2) {}

    T access(const int i) const {
        return this->line[i];
    }

    // left を起点として初項a, 公差d，長さlen の等差数列を加算する
    void add(int left, const int len, const T a, const T d) {
        if (len <= 0) {
            return;
        }
        left %= this->N;
        const int right = left + len;
        this->line[left] += a;
        this->line[left + 1] += d - a;
        this->line[right] -= d * (right - left) + a;
        this->line[right + 1] += d * (right - left - 1) + a;
    }

    // left を起点として初項a, 公差d，長さlen の等差数列を加算する
    // 配列の長さを超えたら 0 に戻る
    void add_circular(int left, const int len, const T a, const T d) {
        left = left % this->N;
        // left から 末尾まで
        const int first = std::min(len, this->N - left);
        this->add(left, first, a, d);

        // 残りの更新すべき長さ
        const int rem = len - first;
        if (rem <= 0) {
            return;
        }

        const int fullCycles = rem / this->N;
        const int remainder = rem % this->N;
        if (fullCycles > 0) {
            const T x = fullCycles * (a + first * d) + d * this->N * (fullCycles * (fullCycles - 1) / 2);
            this->add(0, this->N, x, fullCycles * d);
        }

        if (remainder > 0) {
            this->add(0, remainder, a + (first + fullCycles * this->N) * d, d);
        }
    }

    void build() {
        for (int _ = 0; _ < 2; _++) {
            for (int i = 1; i < this->N; ++i) {
                this->line[i] += this->line[i - 1];
            }
        }
    }
};

LL dist(int from, int to, int M) {
    if (to >= from) {
        return to - from;
    } else {
        return M - (from - to);
    }
}

LL solve(const int N, const int M, const vector<int> &A) {
    ImosArithmeticSequence<LL> imos(M);

    FOR(i, 1, N) {
        const LL d = dist(A[i - 1], A[i], M);
        const int a = M - d;
        imos.add_circular(A[i] + 1, a, d, 0);
        imos.add_circular(A[i] + 1 + a, M - a, M - a, -1);
    }
    imos.build();

    LL ans = LINF;
    FOR(i, 0, M) {
        chmin(ans, imos.access(i));
    }
    return ans;
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, M;
    cin >> N >> M;
    vector<int> A(N);
    FOR(i, 0, N) {
        cin >> A[i];
        A[i]--;
    }
    print(solve(N, M, A));

    return 0;
}
