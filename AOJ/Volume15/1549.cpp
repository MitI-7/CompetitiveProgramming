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
bool is_bit_on(const unsigned long long bit, const unsigned int i) { return (bit >> i) & 1u; }
unsigned long long bit_set(const unsigned long long bit, const unsigned int i, const unsigned int b) {
    assert(b == 0 or b == 1);
    if (b == 0) { return bit & ~(1ull << i); }
    else        {return bit | (1ull << i); }
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

#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <math.h>
#include <string>
#include <queue>
#include <stack>
#include <assert.h>


enum {
    NOTFOUND = 0xFFFFFFFFFFFFFFFFLLU
};

class SuccinctBitVector {
private:
    uint64_t size;                // ビットベクトルのサイズ
    uint32_t blockBitNum = 64;
    std::vector<uint64_t> B;            // ビットベクトル

    uint32_t LEVEL_L = 65536;
    uint32_t LEVEL_S = 256;
    std::vector<uint64_t> L;            // 大ブロック
    std::vector<uint16_t> S;            // 小ブロック

    uint64_t numOne = 0;                // 1bitの数

public:
    SuccinctBitVector(uint64_t n) : size(n) {
        const uint64_t s = (n + blockBitNum - 1) / blockBitNum + 1;   // ceil(n, blockSize)
        this->B.assign(s, 0);
        this->L.assign(n / LEVEL_L + 1, 0);
        this->S.assign(n / LEVEL_S + 1, 0);
    }

    // B[pos] = bit
    void setBit(uint64_t bit, uint64_t pos) {
        assert(bit == 0 or bit == 1);
        assert(pos < this->size);

        const uint64_t blockPos = pos / blockBitNum;
        const uint64_t offset = pos % blockBitNum;
        if (bit == 1) { B.at(blockPos) |= (1LLU << offset); }
        else          { B.at(blockPos) &= (~(1LLU << offset)); }
    }

    // B[pos]
    uint64_t access(uint64_t pos) const {
        assert(pos < this->size);
        const uint64_t blockPos = pos / blockBitNum;
        const uint64_t offset   = pos % blockBitNum;
        return ((B.at(blockPos) >> offset) & 1);
    }

    uint64_t operator[](uint64_t pos) const {
        return access(pos);
    }

    void build() {
        uint64_t num = 0;
        for (uint64_t i = 0; i <= size; i++){
            if (i % LEVEL_L == 0) {
                L.at(i / LEVEL_L) = num;
            }
            if (i % LEVEL_S == 0) {
                S.at(i / LEVEL_S) = num - L.at(i / LEVEL_L);
            }
            if (i != size and i % blockBitNum == 0) {
                num += this->popCount(this->B.at(i / blockBitNum));
            }
        }
        this-> numOne = num;
    }

    // B[0, pos)のbitの数
    uint64_t rank(uint64_t bit, uint64_t pos) const {
        assert(bit == 0 or bit == 1);
        assert(pos <= this->size);

        if (bit) { return rank1(pos); }
        else     { return pos - rank1(pos); }
    }

    // B[l, r)のbitの数
    int rank(uint64_t bit, uint64_t l, uint64_t r) const {
        return rank(bit, r) - rank(bit, l);
    }

    // rank番目のbitの位置 + 1(rankは1-origin)
    uint64_t select(const uint64_t bit, const uint64_t rank) const {
        assert(bit == 0 or bit == 1);
        assert(rank > 0);
        if (bit == 0 and rank > this->size - this-> numOne) { return NOTFOUND; }
        if (bit == 1 and rank > this-> numOne)              { return NOTFOUND; }

        // 大ブロックL内を検索
        uint64_t large_idx = 0;
        {
            uint64_t left = 0;
            uint64_t right = L.size();
            while (right - left > 1) {
                uint64_t mid = (left + right) / 2;
                uint64_t r = L.at(mid);
                r = (bit) ? r : mid * LEVEL_L - L.at(mid);

                if (r < rank) {
                    left = mid;
                    large_idx = mid;
                } else {
                    right = mid;
                }
            }
        }

        // 小ブロックS内を検索
        uint64_t small_idx = (large_idx * LEVEL_L) / LEVEL_S;
        {
            uint64_t left = (large_idx * LEVEL_L) / LEVEL_S;
            uint64_t right = std::min(((large_idx  + 1) * LEVEL_L) / LEVEL_S, S.size());
            while (right - left > 1) {
                uint64_t mid = (left + right) / 2;
                uint64_t r = L.at(large_idx) + S.at(mid);
                r = (bit) ? r :mid * LEVEL_S - r;

                if (r < rank) {
                    left = mid;
                    small_idx = mid;
                } else {
                    right = mid;
                }
            }
        }

        // Bをブロック単位で順番に探索
        uint64_t rank_pos = 0;
        {
            const uint64_t begin_block_idx = (small_idx * LEVEL_S) / blockBitNum;
            uint64_t total_bit = L.at(large_idx) + S.at(small_idx);
            if (bit == 0) {
                total_bit = small_idx * LEVEL_S - total_bit;
            }
            for (uint64_t i = 0;; ++i) {
                uint64_t b = popCount(B.at(begin_block_idx + i));
                if (bit == 0) {
                    b = blockBitNum - b;
                }
                if (total_bit + b >= rank) {
                    uint64_t block = (bit) ? B.at(begin_block_idx + i) : ~B.at(begin_block_idx + i);
                    rank_pos = (begin_block_idx + i) * blockBitNum + selectInBlock(block, rank - total_bit);
                    break;
                }
                total_bit += b;
            }
        }

        return rank_pos + 1;
    }

    uint64_t getNumOne() const {
        return numOne;
    }

    void debug() const {
        std::cout << "LEVEL_L(" << L.size() << ")" << std::endl;
        for (uint64_t i = 0 ; i < L.size(); ++i) {
            std::cout << L.at(i) << ", ";
        }
        std::cout << std::endl;
        std::cout << "LEVEL_S(" << S.size() << ")" << std::endl;
        for (uint64_t i = 0 ; i < S.size(); ++i) {
            std::cout << S.at(i) << ", ";
        }
        std::cout << std::endl;
    }

private:
    uint64_t rank1(uint64_t pos) const {
        uint64_t rank = L.at(pos / LEVEL_L) + S.at(pos / LEVEL_S);

        const uint64_t begin = (pos / LEVEL_S) * LEVEL_S / blockBitNum;
        const uint64_t end = pos / blockBitNum;
        for (uint64_t i = begin; i < end; ++i) {
            rank += popCount(this->B.at(i));
        }
        const uint64_t remain = (pos % LEVEL_S) % blockBitNum;
        rank += popCount(this->B.at(end) & ((1LLU << remain) - 1));

        return rank;
    }

    uint64_t popCount(uint64_t x) const {
        x = (x & 0x5555555555555555ULL) + ((x >> 1) & 0x5555555555555555ULL);
        x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
        x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
        x = x + (x >>  8);
        x = x + (x >> 16);
        x = x + (x >> 32);
        return x & 0x7FLLU;
    }

    uint64_t selectInBlock(uint64_t x, uint64_t rank) const {
        uint64_t x1 = x - ((x & 0xAAAAAAAAAAAAAAAALLU) >> 1);
        uint64_t x2 = (x1 & 0x3333333333333333LLU) + ((x1 >> 2) & 0x3333333333333333LLU);
        uint64_t x3 = (x2 + (x2 >> 4)) & 0x0F0F0F0F0F0F0F0FLLU;

        uint64_t pos = 0;
        for (;;  pos += 8){
            uint64_t rank_next = (x3 >> pos) & 0xFFLLU;
            if (rank <= rank_next) break;
            rank -= rank_next;
        }

        uint64_t v2 = (x2 >> pos) & 0xFLLU;
        if (rank > v2) {
            rank -= v2;
            pos += 4;
        }

        uint64_t v1 = (x1 >> pos) & 0x3LLU;
        if (rank > v1){
            rank -= v1;
            pos += 2;
        }

        uint64_t v0  = (x >> pos) & 0x1LLU;
        if (v0 < rank){
            rank -= v0;
            pos += 1;
        }

        return pos;
    }
};


class WaveletMatrix {
private:
    std::vector<SuccinctBitVector> bit_arrays;
    std::vector<uint64_t> begin_one;                    // 各bitに着目したときの1の開始位置
    std::map<uint64_t, uint64_t> begin_alphabet;        // 最後のソートされた配列で各文字の開始位置
    std::vector<std::vector<uint64_t>> cumulative_sum;  // 各bitに着目したときの累積和

    uint64_t size;                                 // 与えられた配列のサイズ
    uint64_t maximum_element;                      // 文字数
    uint64_t bit_size;                             // 文字を表すのに必要なbit数

public:
    WaveletMatrix() {}

    WaveletMatrix(const std::vector<uint64_t> &array) {
        build(array);
    }

    void build(std::vector<uint64_t> array) {
        assert(!array.empty());
        this->size = array.size();
        this->maximum_element = *max_element(array.begin(), array.end()) + 1;
        this->bit_size = get_num_of_bit(this->maximum_element);
        if (this->bit_size == 0) {
            this->bit_size = 1;
        }

        this->bit_arrays.resize(this->bit_size, SuccinctBitVector(this->size));
        this->begin_one.resize(this->bit_size);
        this->cumulative_sum.resize(this->bit_size + 1, std::vector<uint64_t>(size + 1, 0));

        for (uint64_t j = 0; j < array.size(); ++j) {
            this->cumulative_sum.at(0).at(j + 1) = this->cumulative_sum.at(0).at(j) + array[j];
        }

        for (uint64_t depth = 0; depth < this->bit_size; ++depth) {
            std::vector<uint64_t> zero, one;
            for (uint64_t i = 0; i < this->size; ++i) {
                const uint64_t bit = (array[i] >> (this->bit_size - depth - 1u)) & 1u;
                if (bit) {
                    one.push_back(array[i]);
                    this->bit_arrays[depth].setBit(1, i);
                } else {
                    zero.push_back(array[i]);
                }
            }
            this->bit_arrays[depth].build();
            this->begin_one[depth] = zero.size();

            array = std::move(zero);
            array.insert(array.end(), one.begin(), one.end());

            for (uint64_t j = 0; j < array.size(); ++j) {
                this->cumulative_sum.at(depth + 1).at(j + 1) = this->cumulative_sum.at(depth + 1).at(j) + array.at(j);
            }
        }

        // ソートされた配列内での各文字の位置を取得
        for (int i = array.size() - 1; i >= 0; --i) {
            this->begin_alphabet[array.at(i)] = i;
        }
    }

    // T[begin_pos, end_pos)でx <= c < yを満たす最大のcを返す
    uint64_t prevValue(const uint64_t begin_pos, const uint64_t end_pos, const uint64_t x, uint64_t y) const {
        assert(end_pos <= size);
//        const uint64_t num = end_pos - begin_pos;

        if (x >= y or y == 0) {
            return NOTFOUND;
        }
        if (y > maximum_element) {
            y = maximum_element;
        }

        if (begin_pos >= end_pos) {
            return NOTFOUND;
        }
        if (x >= maximum_element || end_pos == 0) {
            return NOTFOUND;
        }

        y--; // x <= c <= yにする

        std::stack<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, bool>> s;   // (begin, end, depth, c, tight)
        s.emplace(std::make_tuple(begin_pos, end_pos, 0, 0, true));

        while (not s.empty()) {
            uint64_t b, e, depth, c;
            bool tight;
            std::tie(b, e, depth, c, tight) = s.top();
            s.pop();

            if (depth == bit_size) {
                if (c >= x) {
                    return c;
                }
                continue;
            }

            const uint64_t bit = (y >> (bit_size - depth - 1)) & 1;

            const uint64_t rank0_begin = this->bit_arrays.at(depth).rank(0, b);
            const uint64_t rank0_end = this->bit_arrays.at(depth).rank(0, e);
            const uint64_t rank1_begin = b - rank0_begin;
            const uint64_t rank1_end = e - rank0_end;

            // d番目のbitが0のものを使う
            const uint64_t b0 = rank0_begin;
            const uint64_t e0 = rank0_end;
            if (b0 != e0) { // 範囲がつぶれてない
                const uint64_t c0 = ((c << 1) | 0);
                s.emplace(std::make_tuple(b0, e0, depth + 1, c0, tight and bit == 0));
            }

            // d番目のbitが1のものを使う
            const uint64_t b1 = this->begin_one.at(depth) + rank1_begin;
            const uint64_t e1 = this->begin_one.at(depth) + rank1_end;
            if (b1 != e1) {
                if (not tight or bit == 1) {
                    const auto c1 = ((c << 1) | 1);
                    s.emplace(std::make_tuple(b1, e1, depth + 1, c1, tight));
                }
            }
        }

        return NOTFOUND;
    }

    // T[begin_pos, end_pos)でx <= c < yを満たす最小のcを返す
    uint64_t nextValue(const uint64_t begin_pos, const uint64_t end_pos, const uint64_t x, const uint64_t y) const {
        assert(end_pos <= size);
//        const uint64_t num = end_pos - begin_pos;

        if (x >= y or y == 0) {
            return NOTFOUND;
        }

        if (begin_pos >= end_pos) {
            return NOTFOUND;
        }
        if (x >= maximum_element || end_pos == 0) {
            return NOTFOUND;
        }

        std::stack<std::tuple<uint64_t, uint64_t, uint64_t, uint64_t, bool>> s;   // (begin, end, depth, c, tight)
        s.emplace(std::make_tuple(begin_pos, end_pos, 0, 0, true));

        while (not s.empty()) {
            uint64_t b, e, depth, c;
            bool tight;
            std::tie(b, e, depth, c, tight) = s.top();
            s.pop();

            if (depth == bit_size) {
                if (c < y) {
                    return c;
                }
                continue;
            }

            const uint64_t bit = (x >> (bit_size - depth - 1)) & 1;

            const uint64_t rank0_begin = this->bit_arrays.at(depth).rank(0, b);
            const uint64_t rank0_end = this->bit_arrays.at(depth).rank(0, e);
            const uint64_t rank1_begin = b - rank0_begin;
            const uint64_t rank1_end = e - rank0_end;

            // d番目のbitが1のものを使う
            const uint64_t b1 = this->begin_one.at(depth) + rank1_begin;
            const uint64_t e1 = this->begin_one.at(depth) + rank1_end;
            if (b1 != e1) {
                const auto c1 = ((c << 1) | 1);
                s.emplace(std::make_tuple(b1, e1, depth + 1, c1, tight and bit == 1));
            }

            // d番目のbitが0のものを使う
            const uint64_t b0 = rank0_begin;
            const uint64_t e0 = rank0_end;
            if (b0 != e0) {
                if (not tight or bit == 0) {
                    const uint64_t c0 = ((c << 1) | 0);
                    s.emplace(std::make_tuple(b0, e0, depth + 1, c0, tight));
                }
            }
        }

        return NOTFOUND;
    }
private:
    uint64_t get_num_of_bit(uint64_t x) const {
        if (x == 0) return 0;
        x--;
        uint64_t bit_num = 0;
        while (x >> bit_num) {
            ++bit_num;
        }
        return bit_num;
    }
};

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);

    int N, Q;
    cin >> N;
    vector<uint64_t> A(N);
    for (int i = 0; i < N; ++i) {
        cin >> A[i];
    }

    WaveletMatrix wm(A);

    cin >> Q;
    for (int i = 0; i < Q; ++i) {
        uint64_t L, R, D;
        cin >> L >> R >> D;
        R++;

        uint64_t ans = LINF;
        // T[begin_pos, end_pos)でx <= c < yを満たす最大のcを返す
        auto a1 = wm.prevValue(L, R, 0, D);
        if (a1 != NOTFOUND) {
            ans = min(ans, D - a1);
        }
        // T[begin_pos, end_pos)でx <= c < yを満たす最小のcを返す
        auto a2 = wm.nextValue(L, R, D, 1000100);
        if (a2 != NOTFOUND) {
            ans = min(ans, a2 - D);
        }

        cout << ans << endl;
    }

    return 0;
}
