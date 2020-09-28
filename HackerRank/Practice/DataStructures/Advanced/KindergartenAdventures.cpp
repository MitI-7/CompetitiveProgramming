#include <iostream>
#include <array>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <math.h>
#include <string>
#include <climits>
#include <assert.h>
#include <iomanip>
#include <bitset>
#include <queue>
#include <deque>
#include <stack>
#include <functional>
#include <fstream>
#include <random>

#define LEN(x) (long long)(x.size())
#define FOR(i, a, n) for(int i=(a);i<(n); ++i)
#define FOE(i, a) for(auto i : a)
#define ALL(c) (c).begin(), (c).end()
#define RALL(c) (c).rbegin(), (c).rend()
#define SUM(x) std::accumulate(ALL(x), 0LL)
#define MIN(v) *std::min_element(v.begin(), v.end())
#define MAX(v) *std::max_element(v.begin(), v.end())
#define EXIST(v, x) (std::find(v.begin(), v.end(), x) != v.end())
#define BIT_COUNT(bit) (__builtin_popcount(bit))

typedef long long LL;
template<typename T> std::vector<T> make_v(size_t a){return std::vector<T>(a);}
template<typename T,typename... Ts> auto make_v(size_t a, Ts... ts){ return std::vector<decltype(make_v<T>(ts...))>(a,make_v<T>(ts...));}    // C++14
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value==0>::type fill_v(T &t,const V &v){t=v;}
template<typename T,typename V> typename std::enable_if<std::is_class<T>::value!=0>::type fill_v(T &t,const V &v){for(auto &e:t) fill_v(e,v);}
template<class T> inline T ceil(T a, T b) { return (a + b - 1) / b; }
void print() { std::cout << std::endl; }
template <class Head, class... Tail> void print(Head&& head, Tail&&... tail) { std::cout << head; if (sizeof...(tail) != 0) {std::cout << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void print(std::vector<T> &v) {for (auto& a : v) { std::cout << a; if (&a != &v.back()) {std::cout << " ";} }std::cout << std::endl;}
template <class T> void print(std::vector<std::vector<T>> &vv) { for (auto& v : vv) { print(v); }}
void debug() { std::cerr << std::endl; }
template <class Head, class... Tail> void debug(Head&& head, Tail&&... tail) { std::cerr << head; if (sizeof...(tail) != 0) {std::cerr << " ";} print(std::forward<Tail>(tail)...); }
template <class T> void debug(std::vector<T> &v) {for (auto& a : v) { std::cerr << a; if (&a != &v.back()) {std::cerr << " ";} }std::cerr << std::endl;}
template <class T> void debug(std::vector<std::vector<T>> &vv) { for (auto& v : vv) { print(v); }}
inline bool inside(long long y, long long x, long long H, long long W) {return 0 <= y and y < H and 0 <= x and x < W; }
template<class T> inline double euclidean_distance(T y1, T x1, T y2, T x2) { return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)); }
template<class T> inline double manhattan_distance(T y1, T x1, T y2, T x2) { return abs(x1 - x2) + abs(y1 - y2); }
template<typename T> T &chmin(T &a, const T &b) { return a = std::min(a, b); }
template<typename T> T &chmax(T &a, const T &b) { return a = std::max(a, b); }

template<class T> inline std::vector<T> unique(std::vector<T> v) {
    sort(v.begin(), v.end());
    v.erase(unique(v.begin(), v.end()), v.end());
    return v;
}

// 初項s交差d長さnの数列の和
long long sum_of_arithmetic_progression(long long s, long long d, long long n) {
    return n * (2 * s + (n - 1) * d) / 2;
}

// xが2の階乗かどうか判定
bool is_power_of_two(long long x) {
    return !(x & (x - 1));
}

long long gcd(long long a, long long b) {
    if (b == 0) { return a; }
    return gcd(b, a % b);
}

long long gcd(std::vector<long long> &v) {
    long long ans = v[0];
    for (int i = 1; i < (int) v.size(); ++i) {
        ans = gcd(ans, v[i]);
    }
    return ans;
}

long long lcm(long long a, long long b) {
    long long g = gcd(a, b);
    return a / g * b;
}

const int INF = 1u << 30u;  // 1,073,741,824
const long long LINF = 1ull << 60u;
const double EPS = 1e-9;
const long double PI = acos(-1.0);
const std::vector<int> dy2 = {0, 1}, dx2 = {1, 0};
const std::vector<int> dy4 = {0, 1, 0, -1}, dx4 = {1, 0, -1, 0};
const std::vector<int> dy8 = {0, -1, 0, 1, 1, -1, -1, 1}, dx8 = {1, 0, -1, 0, 1, 1, -1, -1};

using namespace std;

class Circle {
public:
    unsigned int n;
    vector<long long> circle;
    vector<long long> dp;
    long long total = 0;

public:
    Circle(vector<long long> circle) : n(circle.size()), circle(circle) {
        this->dp.resize(n * 2 + 1, 0);
        for (int i = 0; i < n * 2; ++i) {
            this->dp[i + 1] = this->dp[i] + circle[i % n];
            this->total += circle[i % n];
        }
        this->total /= 2;
    }

    long long get(int i) const {
        return circle[i % this->n];
    }

    // iの右のインデックス
    int left(int i) const {
        return (i - 1 + this->n) % this->n;
    }

    // iのk個右のインデックス
    int left_k(int i, int k) const {
        assert(k >= 0);
        k %= this->n;
        return (i + k) % this->n;
    }

    // iの左のインデックス
    int right(int i) const {
        return (i + 1) % this->n;
    }

    // iのk個左のインデックス
    int right_k(int i, int k) const {
        assert(k >= 0);
        k %= this->n;
        return (i - k + this->n) % this->n;
    }

    // [i, j)の距離
    int d(int i, int j) {
        assert(i < j);
        if (i < j) {
            return j - i;
        }
        else {
            return this->n - i + j - 1;
        }
    }

    // [i, j)の和
    long long distance(int i, int j) const {
        if (i > j) {
            j += this->n;
        }

        i %= 2 * this->n;
        j %= 2 * this->n;

        return this->dp[j] - this->dp[i];
    }
};

// 円環状でのimos
class ImosCircle {
public:
    const int N;
    std::vector<int> line;

    ImosCircle(int N) : N(N) {
        this->line.resize(N + 1, 0);
    }

    // [left, right]を+1する
    // 閉区間に注意
    void add(int left, int right) {
        if (left <= right) {
            line[left]++;
            line[right + 1]--;
        }
        else {
            line[left]++;
            line[this->N]--;

            line[0]++;
            line[right + 1]--;
        }
    }

    void build() {
        for (int i = 1; i < line.size(); ++i) {
            line[i] += line[i - 1];
        }
    }

    void debug() {
        for (int i = 0; i < line.size(); ++i) {
            std::cout << line.at(i) << " ";
        }
        std::cout << std::endl;
    }
};

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    int N;
    cin >> N;

    vector<int> T(N, 0);
    for (int i = 0; i < N; ++i) {
        cin >> T[i];
    }

    ImosCircle imos(N);
    for (int i = 0; i < N; ++i) {
        int l = i + 1;
        int r = (i - T[i] + N) % N;

        imos.add(l, r);
    }

    imos.build();

    auto maxi = MAX(imos.line);
    for (int i = 0; i < N; ++i) {
        if (imos.line[i] == maxi) {
            print(i + 1);
            return 0;
        }
    }

    return 0;
}