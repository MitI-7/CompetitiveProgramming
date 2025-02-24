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

class Prime {
public:
    // 素数判定
    // O(sqrt(x))
    bool is_prime(int x) {
        if (x == 2) {
            return true;
        }
        if (x < 2 || x % 2 == 0) {
            return false;
        }

        for (int i = 3; i * i <= x; i += 2) {
            if (x % i == 0) {
                return false;
            }
        }
        return true;
    }


    // nまでの素数のリストを作成(nを含む)
    // O(N log log N)
    std::vector<LL> make_prime_list(const int n) {
        std::vector<bool> is_prime(n + 1, true);
        is_prime[0] = false;
        is_prime[1] = false;

        std::vector<LL> prime_list;
        for (int i = 2; i < n + 1; ++i) {
            if (!is_prime[i]) { continue; }
            prime_list.emplace_back(i);

            for (int j = i + i; j < n + 1; j += i) {
                is_prime[j] = false;
            }
        }
        return prime_list;// 素数のリスト
        //return is_prime;  // すべての数値について素数かどうか
    }

    // 配列 v の要素の素因数を列挙
    // O(maxi log maxi)
    std::vector<int> make_divisor_list_in_list(const std::vector<int> &v, const int maxi) {
        std::vector<bool> used(maxi + 1);
        for (const auto a: v) {
            used[a] = true;
        }

        auto prime_list = make_prime_list(maxi);

        std::vector<int> used_prime_list;
        for (auto p: prime_list) {
            bool is_used_prime = false;
            for (int i = p; i <= maxi; i += p) {
                if (used[i]) {
                    is_used_prime = true;
                    break;
                }
            }
            if (is_used_prime) {
                used_prime_list.emplace_back(p);
            }
        }
        return used_prime_list;
    }

    // nを素因数分解する
    // O(n^(1/2))
    // prime_factor_decomposition(12) : {2:2, 3:1}
    std::map<long long, long long> prime_factor_decomposition(long long n) {
        std::map<long long, long long> m;
        while (n > 1) {
            bool findFactor = false;
            for (long long i = 2; i * i <= n; ++i) {
                if (n % i == 0) {
                    m[i]++;
                    n /= i;
                    findFactor = true;
                    break;
                }
            }
            if (not findFactor) {
                m[n]++;
                break;
            }
        }
        return m;
    }
};


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    LL N;
    cin >> N;

    Prime prime;
    auto pl1 = prime.make_prime_list(20100);
    auto pl2 = prime.make_prime_list(2000100);

    LL ans = 0;
    FOR(i, 0, LEN(pl1)) {
        FOR(j, i + 1, LEN(pl2)) {
            if (pl1[i] * pl1[i] <= N and pl1[i] * pl1[i] * pl2[j] <= N) {
                if (pl1[i] * pl1[i] * pl2[j] * pl2[j] <= N) {
                    ans++;
                }
            }
        }
    }

    FOR(i, 0, LEN(pl1)) {
        if (pl1[i] * pl1[i] * pl1[i] * pl1[i] * pl1[i] * pl1[i] * pl1[i] * pl1[i] <= N) {
            ans++;
        }
        else {
            break;
        }
    }
    print(ans);

    return 0;
}
