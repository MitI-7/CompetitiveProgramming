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

#include <array>
#include <cassert>
#include <limits>
#include <memory>
#include <vector>

template<typename T>
class Node {
public:
    T x;               // 葉の値
    int count;         // このノードを通る回数
    int count_distinct;// このノードを頂点とする葉の個数(=種類数)
    T total;           // 子供の値の合計

    // 左の子と右の子
    std::array<std::unique_ptr<Node>, 2> child = {nullptr, nullptr};

    // 葉のとき，左の葉と右の葉を指す（存在しない場合は DUMMYを指す）
    Node *prev;
    Node *next;

    Node *parent;

    // 左の子を持たないときは、この node を根とする部分木における最小の葉を指す
    // 右の子を持たないときは、この node を根とする部分木における最大の葉を指す
    // Trie が空のときは DUMMY を指す
    Node *jump;

    Node() : x(0), count(0), count_distinct(0), total(0), prev(nullptr), next(nullptr), parent(nullptr), jump(nullptr) {}

    Node(const T x, int count) : x(x), count(count), count_distinct(0), total(0), prev(nullptr), next(nullptr), parent(nullptr), jump(nullptr){};
};

template<typename T = uint64_t, int bit_size = 64>
class BinaryTrie {
private:
public:
    std::unique_ptr<Node<T>> root;
    const T NOTFOUND = std::numeric_limits<T>::max();
    Node<T> DUMMY;

    BinaryTrie() {
        this->root = std::make_unique<Node<T>>();
        root->jump = &DUMMY;
        DUMMY.jump = &DUMMY;
        DUMMY.x = NOTFOUND;
        DUMMY.prev = DUMMY.next = &DUMMY;
    }

    // 集合の要素数
    [[nodiscard]] int size() const {
        return this->root->count;
    }

    // 集合の種類数(= 葉の個数)
    [[nodiscard]] int distinct() const {
        return this->root->count_distinct;
    }

    [[nodiscard]] bool empty() const {
        return this->root->count == 0;
    }

    // x を num 個挿入する
    void insert(const T x, const int num = 1) {
        assert(x >= 0);
        auto node = this->root.get();
        const bool exist = this->exist(x);

        node->count += num;
        node->count_distinct += not exist;
        node->total += x * num;


        int i = bit_size - 1;
        // 木の終端ノードにたどり着くまで下る
        for (; i >= 0; --i) {
            const int b = this->get_ith_bit(x, i);
            if (node->child[b] == nullptr) {
                break;
            }
            node = node->child[b].get();
            assert(node->count >= 1);
            node->count += num;
            node->count_distinct += not exist;
            node->total += x * num;
        }
        // すでに葉がある
        if (i == -1) {
            assert(node->x == x);
            return;
        }

        // x の左の葉と右の葉を取得
        assert(node->jump != nullptr);
        const int b = this->get_ith_bit(x, i);
        auto *left_leaf = (b == 1) ? node->jump : node->jump->prev;
        auto *right_leaf = left_leaf->next;
        node->jump = nullptr;
        assert(left_leaf != nullptr);

        // 葉までの経路を作る
        for (; i >= 0; --i) {
            const int b = this->get_ith_bit(x, i);
            assert(node->child[b] == nullptr);
            node->child[b] = std::make_unique<Node<T>>();
            node->child[b]->parent = node;
            node = node->child[b].get();
            node->count += num;
            node->count_distinct++;
            node->total += x * num;
        }
        node->x = x;

        // x を連結リストに追加
        node->prev = left_leaf;
        node->next = right_leaf;
        left_leaf->next = node;
        right_leaf->prev = node;

        // 根に戻りながら，jump を更新する
        auto u = node->parent;
        while (u != nullptr) {
            if ((u->child[0] == nullptr and (u->jump == nullptr or u->jump->x > x)) or
                (u->child[1] == nullptr and (u->jump == nullptr or u->jump->x < x))) {
                u->jump = node;
            }
            u = u->parent;
        }
    }

    // x を num 個削除する
    // x が num 個未満しかない場合はすべて削除する
    void erase(const T x, int num = 1) {
        assert(x >= 0);
        const int num_x = this->count(x);
        if (num_x == 0) {
            return;
        }

        num = std::min(num, num_x);

        auto node = this->root.get();
        node->count -= num;
        node->count_distinct -= (num == num_x);
        node->total -= x * num;

        int i = bit_size - 1;

        // x を含む葉 u を見つける
        for (; i >= 0; --i) {
            int b = this->get_ith_bit(x, i);
            assert(node->child[b] != nullptr);
            node = node->child[b].get();
            assert(node->count > 0);
            node->count -= num;
            node->count_distinct -= (num == num_x);
            node->total -= x * num;
        }
        assert(node->x == x);// 葉にいる

        // x が残るときは終了
        if (num < num_x) {
            return;
        }

        // node を連結リストから削除する
        node->prev->next = node->next;// 自分の左は自分を指しているので，右を指すように更新
        node->next->prev = node->prev;// 自分の右の自分を指しているので，左を指すように更新

        // node から根へ上り，不要なノードを削除する
        auto u = node;
        for (i = 0; i < bit_size; ++i) {
            int b = this->get_ith_bit(x, i);
            u = u->parent;
            u->child[b].release();
            u->child[b] = nullptr;
            // 反対の子供が存在すれば終了
            if (u->child[1 - b] != nullptr) {
                break;
            }
        }

        // jump を更新する
        int b = this->get_ith_bit(x, i);
        assert(u->child[b] == nullptr);
        if (u->child[0] == nullptr) {
            u->jump = node->next;
        } else {
            u->jump = node->prev;
        }

        u = u->parent;
        i++;
        for (; i < bit_size; ++i) {
            b = this->get_ith_bit(x, i);
            if (u->jump == node) {
                if (u->child[0] == nullptr) {
                    u->jump = node->next;
                } else {
                    u->jump = node->prev;
                }
            }
            assert(u->count > 0);
            u = u->parent;
        }
    }

    std::pair<T, T> find_median() {
        const int m = this->size();
        assert(m > 0);
        if (m % 2 == 0) {
            return {this->find_kth_min_element(m / 2 - 1), this->find_kth_min_element(m / 2)};
        } else {
            return {this->find_kth_min_element(m / 2), this->find_kth_min_element(m / 2)};
        }
    }

    // 木にない値のうち，小さい方から k 番目の値を取得(0-origin)
    T find_mex(long long k) const {
        long long maxi_leaf = (long long) 1 << bit_size;

        // k 番目の値は木の外側にある
        if (k + 1 >= maxi_leaf - this->root.get()->count_distinct) {
            return (k - this->root.get()->count_distinct) + maxi_leaf;
        }

        T ans = 0;
        maxi_leaf /= 2;
        auto node = this->root.get();
        for (int i = bit_size - 1; i >= 0; --i) {
            const int num_left_leaf = (node->child[0] == nullptr) ? 0 : node->child[0]->count_distinct;

            // 左側の部分木内にある
            if (k + 1 <= maxi_leaf - num_left_leaf) {
                if (node->child[0] == nullptr) {
                    ans += k;
                    break;
                }
                node = node->child[0].get();
            } else {
                k -= (maxi_leaf - num_left_leaf);

                ans |= ((T) 1 << i);
                if (node->child[1] == nullptr) {
                    ans += k;
                    break;
                }
                node = node->child[1].get();
            }
            maxi_leaf /= 2;
        }

        return ans;
    }

    // vがあるか
    bool exist(const T x) const {
        assert(x >= 0);
        return this->count(x) > 0;
    }

    // x の出現回数
    int count(const T x) const {
        assert(x >= 0);
        auto node = this->root.get();
        for (int i = bit_size - 1; i >= 0; --i) {
            const auto b = this->get_ith_bit(x, i);
            if (node->child[b] == nullptr) {
                return 0;
            }
            node = node->child[b].get();
            assert(node->count > 0);
        }
        assert(node->x == x);
        assert(node->count > 0);
        return node->count;
    }

    // x より小さい値の出現回数
    long long count_less_than(const T x) const {
        assert(x >= 0);
        long long count = 0;
        auto node = this->root.get();

        for (int i = bit_size - 1; i >= 0; --i) {
            const auto b = this->get_ith_bit(x, i);
            // bit が 0 の方にある出現回数をすべて足す
            if (b == 1 and node->child[0] != nullptr) {
                count += node->child[0]->count;
            }
            if (node->child[b] == nullptr) {
                break;
            }
            node = node->child[b].get();
        }

        return count;
    }

    // x より大きい値の出現回数
    int count_more_than(const T x) const {
        assert(x >= 0);
        return this->size() - this->count_less_than(x) - this->count(x);
    }

    // 集合内で最大の値
    T find_max_element() const {
        return this->find_kth_max_element(0);
    }

    // 集合内で最小の値
    T find_min_element() const {
        return this->find_kth_min_element(0);
    }

    // 集合内で小さい順に数えて k 番目の値(0-origin)
    // k = 0 で最小値
    T find_kth_min_element(int k) const {
        if (k < 0 or k >= this->size()) {
            return this->NOTFOUND;
        }

        T ans = 0;
        auto node = this->root.get();
        for (int i = bit_size - 1; i >= 0; --i) {

            const bool exist0 = node->child[0] != nullptr;
            const bool exist1 = node->child[1] != nullptr;
            assert(exist0 or exist1);

            bool go_node0;
            if (exist0 and exist1) {
                if (k < node->child[0]->count) {
                    go_node0 = true;
                } else {
                    go_node0 = false;
                    k -= node->child[0]->count;
                }
            } else {
                go_node0 = exist0;
            }

            if (go_node0) {
                node = node->child[0].get();
            } else {
                ans |= ((T) 1 << i);
                node = node->child[1].get();
            }
        }

        return ans;
    }

    // k 番目に大きい値(0-based)
    // k = 0 で最大値
    T find_kth_max_element(const int k) const {
        if (k < 0 or k >= this->size()) {
            return this->NOTFOUND;
        }
        return this->find_kth_min_element(this->size() - 1 - k);
    }

    // x 以下の要素のうち，大きい方から k 番目の値
    T find_kth_max_element_leq(const int k, const T x) {
        int num = this->count_more_than(x);
        return this->find_kth_max_element(num + k);
    }

    // x 以上の要素のうち，小さい方から k 番目の値
    T find_kth_min_element_geq(const int k, const T x) {
        int num = this->count_less_than(x);
        return this->find_kth_min_element(num + k);
    }

    // x 以下で最大のノード
    const Node<T> *predecessor(const T x) const {
        assert(x >= 0);

        auto node = this->root.get();
        for (int i = bit_size - 1; i >= 0; --i) {
            const auto b = this->get_ith_bit(x, i);
            if (node->child[b] == nullptr) {
                if (b == 1) {
                    // node を根とする部分木における最小の葉を指す
                    return std::ref(node->jump);
                } else {
                    return std::ref(node->jump->prev);
                }
            }
            node = node->child[b].get();
        }
        // x を見つけた
        assert(node->x == x);
        return std::ref(node);
    }

    // x 以上で最小の値
    const Node<T> *successor(const T x) const {
        assert(x >= 0);

        auto node = this->root.get();
        for (int i = bit_size - 1; i >= 0; --i) {
            const auto b = this->get_ith_bit(x, i);
            if (node->child[b] == nullptr) {
                if (b == 0) {
                    return std::ref(node->jump);
                } else {
                    return std::ref(node->jump->next);
                }
            }
            node = node->child[b].get();
        }
        // x を見つけた
        assert(node->x == x);
        return std::ref(node);
    }

    // 集合内で小さい順に k 個の値の合計
    T sum_of_k_smallest(int k) const {
        if (k <= 0) {
            return 0;
        }
        if (k >= this->size()) {
            return this->root->total;
        }

        T ans = 0;
        auto node = this->root.get();
        for (int i = bit_size - 1; i >= 0; --i) {

            const bool exist0 = node->child[0] != nullptr;
            const bool exist1 = node->child[1] != nullptr;
            assert(exist0 or exist1);

            bool go_node0;
            if (exist0 and exist1) {
                if (k < node->child[0]->count) {
                    go_node0 = true;
                } else {
                    go_node0 = false;
                    k -= node->child[0]->count;
                }
            } else {
                go_node0 = exist0;
            }

            if (go_node0) {
                node = node->child[0].get();
            } else {
                if (exist0) {
                    ans += node->child[0].get()->total;
                }
                node = node->child[1].get();
            }
        }
        ans += node->x * k;
        return ans;
    }

    // 集合内で大きい順に k 個の値の合計
    T sum_ok_k_largest(const int k) const {
        if (k <= 0) {
            return 0;
        }
        if (k >= this->size()) {
            return this->root->total;
        }
        int num_smallest = this->root->count - k;
        return this->root->total - this->sum_of_k_smallest(num_smallest);
    }

    // v^x を最小にするような x をみつける
    T find_xor_min_element(T v) const {
        assert(v >= 0);
        assert(not this->empty());

        auto node = this->root.get();
        T ans = 0;
        for (int i = bit_size - 1; i >= 0; --i) {
            auto b = (v >> (T) i) & 1u;

            const bool exist0 = node->child[0] != nullptr;
            const bool exist1 = node->child[1] != nullptr;
            assert(exist0 or exist1);

            bool go_node0;
            if (exist0 and exist1) {
                go_node0 = (b == 0);
            } else {
                go_node0 = exist0;
            }

            if (go_node0) {
                node = node->child[0].get();
            } else {
                ans |= (1u << (unsigned) i);
                node = node->child[1].get();
            }
        }

        return ans;
    }

    // v 以外で v^x を最小にするような x を求める
    T min_element_xor_without_v(T v) const {
        assert(false);
        return 0;
    }

    // v^x を最大にするような x を求める
    T max_element_xor(const T v) const {
        assert(v >= 0);
        assert(not this->empty());

        auto node = this->root.get();
        T ans = 0;
        for (int i = bit_size - 1; i >= 0; --i) {
            auto b = (v >> (T) i) & 1u;

            const bool exist0 = node->child[0] != nullptr;
            const bool exist1 = node->child[1] != nullptr;
            assert(exist0 or exist1);

            bool go_node0;
            if (exist0 and exist1) {
                go_node0 = (b == 1);
            } else {
                go_node0 = exist0;
            }

            if (go_node0) {
                node = node->child[0].get();
            } else {
                ans |= (1u << (unsigned) i);
                node = node->child[1].get();
            }
        }

        return ans;
    }

    // xorしたときに，小さい方から見てk番目の数(0-based)
    T kth_element_xor(const T v, int k) const {
        assert(v >= 0);
        assert(this->root->count != 0);
        assert(k < this->root->count);
        assert(false);
        return 0;
    }

    // すべての要素について，vをxorした値に変更する
    void xor_all(T v) const {
        assert(v >= 0);
        assert(false);
    }

private:
    // x の i 番目の bit を取得
    int get_ith_bit(const T x, const int i) const {
        return (x >> i) & 1u;
    }
};

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    int N, M;
    LL K;
    cin >> N >> M >> K;
    vector<pair<LL, int>> A(N);
    LL total = 0;
    FOR(i, 0, N) {
        cin >> A[i].first;
        A[i].second = i;
        total += A[i].first;
    }
    sort(ALL(A));

    if (N == M) {
        vector<int> ans(N);
        print(ans);
        return 0;
    }

    BinaryTrie<LL> bt;
    FOR(i, 0, M) {
        bt.insert(A[N - i - 1].first);
    }

    const LL rest = K - total;
    vector<LL> ans(N, -1);

    FOR(i, 0, N) {
        const LL a = A[i].first;

        if (i >= N - M) {
            bt.erase(a);
        }
        if (i == N - M) {
            if (N - M - 1 >= 0) {
                bt.insert(A[N - M - 1].first);
            }
        }

        // iがx票もらったとき勝てるか
        auto can_win = [&](LL x) {
            assert(x <= rest);
            LL now_i = a + x;
            const LL num = bt.count_less_than(now_i + 1);
            const LL need = (now_i + 1) * num - bt.sum_of_k_smallest(num);  // iを負かすために必要な票数
            return need > rest - x;
        };

        if (can_win(0)) {
            ans[A[i].second] = 0;

        }
        else if (not can_win(rest)) {

        }
        else {
            long long left = 0, right = rest;
            assert(not can_win(left));
            assert(can_win(right));
            while (right - left > 1) {
                const auto mid = std::midpoint(left, right);
                if (can_win(mid)) {
                    right = mid;
                } else {
                    left = mid;
                }
            }
            ans[A[i].second] = right;
        }

        if (i >= N - M) {
            bt.insert(a);
        }
    }
    print(ans);

    return 0;
}
