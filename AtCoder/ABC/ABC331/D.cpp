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

//#include <cassert>
//#include <vector>

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

template<typename T>
class CumulativeSum2Dim {
public:
    std::vector<std::vector<T>> memo;

    CumulativeSum2Dim() = default;

    explicit CumulativeSum2Dim(const std::vector<std::vector<T>> &grid) {
        this->build(grid);
    }

    // gridは左上が (0, 0)，右下が(H - 1, W - 1)
    // O(H * W)
    void build(const std::vector<std::vector<T>> &grid) {
        const int height = grid.size();
        const int width = grid[0].size();

        this->memo = std::vector<std::vector<T>>(height + 1, std::vector<T>(width + 1));

        for (int y = 0; y < height; ++y) {
            for (int x = 0; x < width; ++x) {
                this->memo[y + 1][x + 1] = grid[y][x] + this->memo[y + 1][x];
            }
            for (int x = 0; x < width; ++x) {
                this->memo[y + 1][x + 1] += this->memo[y][x + 1];
            }
        }
    }

    // 行 y の区間 [x1, x2) の合計
    T sum_row(const int y, const int x1, const int x2) const {
        return this->sum(y, x1, y + 1, x2);
    }

    // 列 x の区間 [y1, y2) の合計
    T sum_col(const int x, const int y1, const int y2) const {
        return this->sum(y1, x, y2, x + 1);
    }

    // 左上 (y1, x1) から右下 (y2, x2) の合計を返す．(y2, x2)の行と列は含まない
    // 例えば， sum(0, 0, 2, 2) なら (0, 0), (0, 1), (1, 0), (1, 1) の合計を返す
    T sum(const int y1, const int x1, const int y2, const int x2) const {
        assert(y2 >= y1);
        assert(x2 >= x1);
        return this->memo[y2][x2] - this->memo[y2][x1] - this->memo[y1][x2] + this->memo[y1][x1];
    }

    void debug() const {
        for (const auto line: this->memo) {
            for (const auto a: line) {
                std::cout << a << " ";
            }
            std::cout << std::endl;
        }
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, Q;
    cin >> N >> Q;

    auto grid = make_v<LL>(N, N);
    FOR(y, 0, N) {
        string S;
        cin >> S;
        FOR(x, 0, N) {
            if (S[x] == 'B') {
                grid[y][x] = 1;
            }
        }
    }

    CumulativeSum2Dim<LL> cs(grid);

    vector<LL> ans(Q);
    FOR(i, 0, Q) {
        LL Y1, X1, Y2, X2;
        cin >> Y1 >> X1 >> Y2 >> X2;

        LL l = 0;
        if (X1 % N != 0) {
            l = N - X1 % N;
        }
        LL r = 0;
        if (X2 % N != N - 1) {
            r = (X2 % N) + 1;
        }
        LL yoko_loop = ((X2 - r) - (X1 + l) + 1) / N;

        vector<LL> line(N);
        LL total = 0;
        FOR(y, 0, N) {
            line[y] += yoko_loop * cs.sum_row(y % N, 0, N);
            line[y] += cs.sum_row(y % N, N - l, N);
            line[y] += cs.sum_row(y % N, 0, r);
            total += line[y];
        }

        CumulativeSum<LL> cs_line(line);
        // 縦の繰り返し
        LL t = 0;
        if (Y1 % N != 0) {
            t = N - Y1 % N;
        }
        LL d = 0;
        if (Y2 % N != N - 1) {
            d = (Y2 % N) + 1;
        }
        LL tate_loop = ((Y2 - d) - (Y1 + t) + 1) / N;
        total *= tate_loop;

        total += cs_line.sum(N - t, N);
        total += cs_line.sum(0, d);
        ans[i] = total;
    }
    print(ans);

    return 0;
}