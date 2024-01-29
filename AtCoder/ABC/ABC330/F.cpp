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
// 2次元配列上での移動．右，下，左，上，右上，右下，左下，左上
const std::vector<int> dy8 = {0, 1, 0, -1, -1, 1, 1, -1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};
// @formatter:on

using namespace std;


int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    LL N, K;
    cin >> N >> K;

    map<LL, LL> x_count, y_count;
    FOR(i, 0, N) {
        LL X, Y;
        cin >> X >> Y;
        x_count[X]++;
        y_count[Y]++;
    }

    auto mini_step = [](map<LL, LL> &m, LL len) {
        deque<pair<LL, LL>> deq;
        FOE(p, m) {
            deq.emplace_back(p);
        }

        LL step = 0;
        while (deq.back().first - deq.front().first > len) {
            const auto [front_d, front_num] = deq.front();
            const auto [back_d, back_num] = deq.back();

            assert(deq.size() >= 2);
            if (deq.size() == 2) {
                LL dist = (back_d - front_d) - len;
                step += dist * min(front_num, back_num);
                break;
            }
            else {
                assert(deq.size() >= 3);
                const auto [front2_d, front2_num] = deq[1];
                const auto [back2_d, back2_num] = deq[deq.size() - 2];

                if (front_num < back_num) {
                    LL d = front2_d - front_d;
                    if (back_d - len < front2_d) {
                        d = (back_d - len) - front_d;
                    }
                    step += front_num * d;
                    deq.pop_front();
                    deq.pop_front();
                    deq.emplace_front(front2_d, front_num + front2_num);
                }
                else {
                    LL d = back_d - back2_d;
                    if (back2_d < front_d + len) {
                        d = back_d - (front_d + len);
                    }
                    step += back_num * d;
                    deq.pop_back();
                    deq.pop_back();
                    deq.emplace_back(back2_d, back_num + back2_num);
                }
            }
        }
        return step;
    };

    auto ok = [&](long long len) {
        return mini_step(x_count, len) + mini_step(y_count, len) <= K;
    };

    // 条件を満たす最小値を区間(left, right)から探索
    // x x x x x x x o o o o o o o の一番左の o を探す
    long long left = 0, right = INF * 2LL;
    if (ok(left)) {
        print(0);
        return 0;
    }
    assert(ok(right));
    while (right - left > 1) {
        const auto mid = (left + right) / 2;
        if (ok(mid)) {
            right = mid;
        }
        else {
            left = mid;
        }
    }
    print(right);

    return 0;
}