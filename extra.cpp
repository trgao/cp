#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using ll = long long;
using ld = long double;
using bll = __int128;
using namespace std;
using namespace __gnu_pbds;
#define LSOne(S) ((S) & (-S))
typedef tree<pair<ll, ll>,null_type,less<pair<ll, ll>>,rb_tree_tag,tree_order_statistics_node_update> ordered_set;
ll n, m, t, k, q, x, y, l, r, a, b, c, d;
ld d1, d2;
string s, u;

ll pow(ll a, ll b, ll m) {
    ll ans = 1;
    while(b){
        if (b&1) ans = (ans*a) % m;
        b /= 2;
        a = (a*a) % m;
    }
    return ans;
}

void factors(map<ll, ll>& fs, ll n) {
    while (n % 2 == 0) fs[2]++, n = n/2;
    for (ll i = 3; i * i <= n; i = i + 2) {
        while (n % i == 0) fs[i]++, n = n/i;
    }
    if (n > 2) fs[n]++;
}

ll modpow(ll base, ll exp, ll m) {
    base %= m;
    ll result = 1;
    while (exp > 0) {
        if (exp & 1) result = (result * base) % m;
        base = (base * base) % m;
        exp >>= 1;
    }
    return result;
}

//for prime p
ll modinv(ll n, ll p) {
    return modpow(n, p - 2, p);
}

ll mod(ll a, ll m) {                          // returns a (mod m)
    return ((a%m) + m) % m;                        // ensure positive answer
}

ll modPow(ll b, ll p, ll m) {                // assume 0 <= b < m
    if (p == 0) return 1;
    ll ans = modPow(b, p/2, m);                   // this is O(log p)
    ans = mod(ans*ans, m);                         // double it first
    if (p&1) ans = mod(ans*b, m);                  // *b if p is odd
    return ans;                                    // ans always in [0..m-1]
}

ll extEuclid(ll a, ll b, ll &x, ll &y) {    // pass x and y by ref
    ll xx = y = 0;
    ll yy = x = 1;
    while (b) {                                    // repeats until b == 0
        ll q = a/b;
        tie(a, b) = tuple(b, a%b);
        tie(x, xx) = tuple(xx, x-q*xx);
        tie(y, yy) = tuple(yy, y-q*yy);
    }
    return a;                                      // returns gcd(a, b)
}

//for general mod inverse
ll modInverse(ll b, ll m) {                   // returns b^(-1) (mod m)
    ll x, y;
    ll d = extEuclid(b, m, x, y);                 // to get b*x + m*y == d
    if (d != 1) return -1;                         // to indicate failure
    // b*x + m*y == 1, now apply (mod m) to get b*x == 1 (mod m)
    return mod(x, m);
}

ll crt(vector<ll> r, vector<ll> m) {
    // m_t = m_0*m_1*...*m_{n-1}
    ll mt = accumulate(m.begin(), m.end(), 1ll, multiplies<>());
    ll x = 0;
    for (ll i = 0; i < (ll)m.size(); ++i) {
        ll a = mod((ll)r[i] * modInverse(mt/m[i], m[i]), m[i]);
        x = mod(x + (ll)a * (mt/m[i]), mt);
    }
    return x;
}

ll ncrp(ll n, ll r, ll p) {
    if (n < r) return 0;
    if (r == 0) return 1;
    ll fac[n + 1];
    fac[0] = 1;
    for (ll i = 1; i <= n; i++) fac[i] = (fac[i - 1] * i) % p;
    return (fac[n] * modinv(fac[r], p) % p * modinv(fac[n - r], p) % p) % p;
}

ll ncr(ll n, ll r) {
    if (r > n) return 0;
    ll p = 1, k = 1;
    if (n - r < r) r = n - r;
    if (r != 0) {
        while (r) {
            p *= n;
            k *= r;
            ll m = gcd(p, k);
            p /= m;
            k /= m;
            --n;
            --r;
        }
    } else p = 1;
    return p;
}

ll catalan(ll n, ll p) {
    ll cat[n + 1];
    cat[0] = 1;
    for (ll i = 0; i <= n; ++i) cat[i + 1] = ((4 * i + 2) % p * cat[i] % p * modinv(i + 2, p)) % p;
    return cat[n];
}

// Calculating Smallest Prime Factor for every number till MAXN.
// Time Complexity : O(nloglogn)
void sieve(vector<ll>& spf, ll maxn) {
    spf[1] = 1;
    for (ll i = 2; i < maxn; i++) spf[i] = i;
    for (ll i = 4; i < maxn; i += 2) spf[i] = 2;
    for (ll i = 3; i * i < maxn; i++) {
        if (spf[i] == i) {
            for (ll j = i * i; j < maxn; j += i) if (spf[j] == j) spf[j] = i;
        }
    }
}

// A O(log n) function returning prime factorization by dividing by smallest prime factor at every step
set<ll> getFactorization(vector<ll> spf, ll x) {
    set<ll> res;
    while (x != 1) res.insert(spf[x]), x = x / spf[x];
    return res;
}

// Euler totient O(sqrt(n)) (count number of coprime numbers less than n)
ll phi(ll n) {
    ll result = n;
    for (ll i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            while (n % i == 0) n /= i;
            result -= result / i;
        }
    }
    if (n > 1) result -= result / n;
    return result;
}

// O(nlognlogn) euler totient from 1 to n
vector<ll> phi_1_to_n(ll n) {
    vector<ll> phi(n + 1);
    for (ll i = 0; i <= n; i++) phi[i] = i;
    for (ll i = 2; i <= n; i++) if (phi[i] == i) for (int j = i; j <= n; j += i) phi[j] -= phi[j] / i;
    return phi;
}

// faster, just need primes < maxN
set<ll> primeFactors(vector<ll>& ps, ll N) {                         // pre-condition, N >= 1
    set<ll> factors;
    for (ll i = 0; (i < (ll) ps.size()) && (ps[i] * ps[i] <= N); ++i) {
        while (N % ps[i] == 0) {
            N /= ps[i];
            factors.insert(ps[i]);
        }
    }
    if (N != 1) factors.insert(N);
    return factors;
}

ll merge(vector<ll>& arr, vector<ll>& temp, ll left, ll mid, ll right) {
    ll i, j, k;
    ll inv_count = 0;

    i = left;
    j = mid;
    k = left;
    while ((i <= mid - 1) && (j <= right)) {
        if (arr[i] <= arr[j]) temp[k++] = arr[i++];
        else temp[k++] = arr[j++], inv_count = inv_count + (mid - i);
    }
    while (i <= mid - 1) temp[k++] = arr[i++];
    while (j <= right) temp[k++] = arr[j++];
    for (i = left; i <= right; i++) arr[i] = temp[i];
    return inv_count;
}

ll countInv(vector<ll>& arr, vector<ll>& temp, ll left, ll right) {
    ll mid, inv_count = 0;
    if (right > left) {
        mid = (right + left) / 2;
        inv_count += countInv(arr, temp, left, mid);
        inv_count += countInv(arr, temp, mid + 1, right);
        inv_count += merge(arr, temp, left, mid + 1, right);
    }
    return inv_count;
}

ll minSwaps(vector<ll> arr, ll n) {
    vector< pair<ll, ll> > arrPos(n);
    for (ll i = 0; i < n; i++) arrPos[i].first = arr[i], arrPos[i].second = i;
    sort(arrPos.begin(), arrPos.end());
    vector<bool> vis(n, false);
    ll ans = 0;
    for (ll i = 0; i < n; i++) {
        if (vis[i] || arrPos[i].second == i) continue;
        ll cycle_size = 0;
        ll j = i;
        while (!vis[j]) vis[j] = true, j = arrPos[j].second, cycle_size++;
        if (cycle_size > 0) ans += (cycle_size - 1);
    }
    return ans;
}

ll ceil2(ll a, ll b) {
    return (a + b - 1) / b;
}

ll andOperator(ll x, ll y) {
    for (ll i = 0; i < (ll) log2(y) + 1; i++) {
        if (y <= x) return y;
        if (y & (1LL << i)) y &= ~(1LL << i);
    }
    return y;
}

vector<ll> manacher(string t) {
    string s;
    for(auto c: t) s += "#", s += c;
    s += "#";
    ll n = s.size();
    s = "$" + s + "^";
    vector<ll> p(n + 2);
    ll l = 1, r = 1;
    for(ll i = 1; i <= n; i++) {
        p[i] = max(0ll, min(r - i, p[l + (r - i)]));
        while(s[i - p[i]] == s[i + p[i]]) p[i]++;
        if(i + p[i] > r) l = i - p[i], r = i + p[i];
    }
    return vector<ll>(begin(p) + 1, end(p) - 1);
}

// Robin Karp string hashing
ll compute_hash(string& s) {
    const ll p = 31;
    const ll m = 1000000009ll;
    // ll largeprime1 = 1610612741;
    // ll largeprime2 = 201326611;
    ll hash_value = 0;
    ll p_pow = 1;
    for (char c : s) {
        hash_value = (hash_value + (c - 'a' + 1) * p_pow) % m;
        p_pow = (p_pow * p) % m;
    }
    return hash_value;
}

// n eggs, k floors, egg drop dp
ll eggDrop(ll n, ll k) {
    ll eggFloor[n + 1][k + 1];
    for (ll i = 1; i <= n; i++) eggFloor[i][1] = 1, eggFloor[i][0] = 0;
    for (ll j = 1; j <= k; j++) eggFloor[1][j] = j;
    for (ll i = 2; i <= n; i++) {
        for (ll j = 2; j <= k; j++) {
            eggFloor[i][j] = LONG_LONG_MAX;
            for (ll x = 1; x <= j; x++) eggFloor[i][j] = min(eggFloor[i][j], 1 + max(eggFloor[i - 1][x - 1], eggFloor[i][j - x]));
        }
    }
    return eggFloor[n][k];
}

ll dp[11][105][105];
ll mailbox(ll k, ll a, ll b) {
    if (k == 0) return LONG_LONG_MAX;
    if (k == 1) return (b * (b + 1)) / 2 - (a * (a + 1)) / 2;
    if (a == b) return 0;
    ll& ans = dp[k][a][b];
    if (dp[k][a][b] != -1) return ans;
    ans = LONG_LONG_MAX;
    for (ll i = a + 1; i <= b; ++i) ans = min(ans, i + max(mailbox(k - 1, a, i - 1), mailbox(k, i, b)));
    return ans;
}

ll findHamPaths(ll N, vector<set<ll> >& graph) {
    ll dp[N][(1 << N)];
    memset(dp, 0, sizeof dp);
    dp[0][1] = 1;
    for (ll i = 2; i < (1 << N); i++) {
        if ((i & (1 << 0)) == 0) continue;
        if ((i & (1 << (N - 1))) && i != ((1 << N) - 1)) continue;
        for (ll end = 0; end < N; end++) {
            if ((i & (1 << end)) == 0) continue;
            ll prev = i - (1 << end);
            for (ll it : graph[end]) if ((i & (1 << it))) dp[end][i] += dp[it][prev];
        }
    }
    return dp[N - 1][(1 << N) - 1];
}

class SegmentTree {                              // OOP style
private:
    ll n;                                         // n = (ll)A.size()
    vector<ll> A, st, lazy;                                // the arrays

    ll l(ll p) { return  p<<1; }                 // go to left child
    ll r(ll p) { return (p<<1)+1; }              // go to right child

    ll conquer(ll a, ll b) {
        if (a == -1) return b;                       // corner case
        if (b == -1) return a;
        return min(a, b);                            // RMQ
    }

    void build(ll p, ll L, ll R) {              // O(n)
        if (L == R)
            st[p] = A[L];                              // base case
        else {
            ll m = (L+R)/2;
            build(l(p), L  , m);
            build(r(p), m+1, R);
            st[p] = conquer(st[l(p)], st[r(p)]);
        }
    }

    void propagate(ll p, ll L, ll R) {
        if (lazy[p] != -1) {                         // has a lazy flag
            st[p] = lazy[p];                           // [L..R] has same value
            if (L != R)                                // not a leaf
                lazy[l(p)] = lazy[r(p)] = lazy[p];       // propagate downwards
            else                                       // L == R, a single index
                A[L] = lazy[p];                          // time to update this
            lazy[p] = -1;                              // erase lazy flag
        }
    }

    ll RMQ(ll p, ll L, ll R, ll i, ll j) {   // O(log n)
        propagate(p, L, R);                          // lazy propagation
        if (i > j) return -1;                        // infeasible
        if ((L >= i) && (R <= j)) return st[p];      // found the segment
        ll m = (L+R)/2;
        return conquer(RMQ(l(p), L  , m, i          , min(m, j)),
                       RMQ(r(p), m+1, R, max(i, m+1), j        ));
    }

    void update(ll p, ll L, ll R, ll i, ll j, ll val) { // O(log n)
        propagate(p, L, R);                          // lazy propagation
        if (i > j) return;
        if ((L >= i) && (R <= j)) {                  // found the segment
            lazy[p] = val;                             // update this
            propagate(p, L, R);                        // lazy propagation
        }
        else {
            ll m = (L+R)/2;
            update(l(p), L  , m, i          , min(m, j), val);
            update(r(p), m+1, R, max(i, m+1), j        , val);
            ll lsubtree = (lazy[l(p)] != -1) ? lazy[l(p)] : st[l(p)];
            ll rsubtree = (lazy[r(p)] != -1) ? lazy[r(p)] : st[r(p)];
            st[p] = (lsubtree <= rsubtree) ? st[l(p)] : st[r(p)];
        }
    }

public:
    SegmentTree(ll sz) : n(sz), A(n), st(4*n), lazy(4*n, -1) {}

    SegmentTree(const vector<ll> &initialA) : SegmentTree((ll)initialA.size()) {
        A = initialA;
        build(1, 0, n-1);
    }

    void update(ll i, ll j, ll val) { update(1, 0, n-1, i, j, val); }

    ll RMQ(ll i, ll j) { return RMQ(1, 0, n-1, i, j); }
};

class XORSegmentTree {                              // OOP style
private:
    ll n;                                         // n = (ll)A.size()
    vector<bll> A, st, lazy;                                // the arrays

    ll l(ll p) { return  p<<1; }                 // go to left child
    ll r(ll p) { return (p<<1)+1; }              // go to right child

    bll conquer(bll a, bll b) {
        if (a == -1) return b;                       // corner case
        if (b == -1) return a;
        return a ^ b;                            // RMQ
    }

    void build(ll p, ll L, ll R) {              // O(n)
        if (L == R)
            st[p] = A[L];                              // base case
        else {
            ll m = (L+R)/2;
            build(l(p), L  , m);
            build(r(p), m+1, R);
            st[p] = conquer(st[l(p)], st[r(p)]);
        }
    }

    void propagate(ll p, ll L, ll R) {
        if (lazy[p] != -1) {                         // has a lazy flag
            st[p] ^= lazy[p];                           // [L..R] has same value
            if (L != R)                                // not a leaf
                lazy[l(p)] = lazy[r(p)] = lazy[p];       // propagate downwards
            else                                       // L == R, a single index
                A[L] ^= lazy[p];                          // time to update this
            lazy[p] = -1;                              // erase lazy flag
        }
    }

    bll RMQ(ll p, ll L, ll R, ll i, ll j) {   // O(log n)
        propagate(p, L, R);                          // lazy propagation
        if (i > j) return -1;                        // infeasible
        if ((L >= i) && (R <= j)) return st[p];      // found the segment
        ll m = (L+R)/2;
        return conquer(RMQ(l(p), L  , m, i          , min(m, j)),
                       RMQ(r(p), m+1, R, max(i, m+1), j        ));
    }

    void update(ll p, ll L, ll R, ll i, ll j, bll val) { // O(log n)
        propagate(p, L, R);                          // lazy propagation
        if (i > j) return;
        if ((L >= i) && (R <= j)) {                  // found the segment
            lazy[p] = val;                             // update this
            propagate(p, L, R);                        // lazy propagation
        }
        else {
            ll m = (L+R)/2;
            update(l(p), L  , m, i          , min(m, j), val);
            update(r(p), m+1, R, max(i, m+1), j        , val);
            bll lsubtree = (lazy[l(p)] != -1) ? lazy[l(p)] ^ st[l(p)] : st[l(p)];
            bll rsubtree = (lazy[r(p)] != -1) ? lazy[r(p)] ^ st[r(p)] : st[r(p)];
            st[p] = conquer(lsubtree, rsubtree);
        }
    }

public:
    XORSegmentTree(ll sz) : n(sz), A(n), st(4*n), lazy(4*n, -1) {}

    XORSegmentTree(const vector<bll> &initialA) : XORSegmentTree((ll)initialA.size()) {
        A = initialA;
        build(1, 0, n-1);
    }

    void update(ll i, ll j, bll val) { update(1, 0, n-1, i, j, val); }

    bll RMQ(ll i, ll j) { return RMQ(1, 0, n-1, i, j); }
};

// index = 1, s = 0, e = n - 1
class SumSegmentTree {
private:
    ll n;
    vector<ll> a, tree;
public:
    SumSegmentTree(ll sz) {n = sz, a = vector<ll>(n), tree = vector<ll>(4 * n + 1);}
    void buildTree(ll index, ll s, ll e) {
        //base case
        if (s > e) return;
        //reached leaf node
        if (s == e) {
            tree[index] = a[s];
            return;
        }
        //now build the segment tree in bottom up manner
        ll m = (s + e) / 2;
        buildTree(2 * index,s,m);
        buildTree(2 * index + 1,m + 1,e);
        tree[index] = tree[2 * index] + tree[2 * index + 1];
    }

    //function to query the segment tree for RSQ
    ll query(ll index, ll s, ll e, ll qs, ll qe) {
        //base case: if query range is outside the node range
        if (qs > e || s > qe) return 0;
        //complete overlap
        if (s >= qs && e <= qe) return tree[index];
        //now partial overlap case is executed
        ll m = (s + e) / 2;
        ll left_ans = query(2 * index, s, m, qs, qe);
        ll right_ans = query(2 * index + 1, m + 1, e, qs, qe);
        return left_ans + right_ans;
    }

    //function to update a value at position to "pos"
    void updateNode(ll index, ll s, ll e, ll pos, ll val){
        if(pos < s || pos > e) return ;
        if (s == e) {
            tree[index] = val;
            return;
        }
        ll m = (s + e) / 2;
        updateNode(2 * index, s, m, pos, val);
        updateNode(2 * index + 1, m + 1,e , pos, val);
        tree[index] = tree[2 * index] + tree[2 * index + 1];
    }

    //function to update the values in a range
    void updateRange(ll index, ll s, ll e, ll rs, ll re, ll inc) {
        //query range outside the node range
        if (s > re || e < rs) return;
        if (s == e) {
            tree[index] += inc;
            return ;
        }
        ll m = (s + e) / 2;
        updateRange(2 * index, s, m, rs, re, inc);
        updateRange(2 * index + 1, m + 1, e, rs, re, inc);
        tree[index] = tree[2 * index] + tree[2 * index + 1];
    }
};

template<class Fun> class y_combinator_result {
    Fun fun_;
public:
    template<class T> explicit y_combinator_result(T &&fun): fun_(std::forward<T>(fun)) {}
    template<class ...Args> decltype(auto) operator()(Args &&...args) { return fun_(std::ref(*this), std::forward<Args>(args)...); }
};
template<class Fun> decltype(auto) y_combinator(Fun &&fun) { return y_combinator_result<std::decay_t<Fun>>(std::forward<Fun>(fun)); }


struct segment_change {
    // Use a sentinel value rather than a boolean to save significant memory (4-8 bytes per object).
    static const ll SENTINEL = numeric_limits<ll>::lowest();

    // Note that to_set goes first, and to_add goes after.
    // TODO: check if these values can overflow ll.
    ll to_set, to_add;

    // TODO: make sure the default constructor is the identity segment_change.
    segment_change(ll _to_add = 0, ll _to_set = SENTINEL) : to_set(_to_set), to_add(_to_add) {}

    bool has_set() const {
        return to_set != SENTINEL;
    }

    bool has_change() const {
        return has_set() || to_add != 0;
    }

    // Return the combined result of applying this segment_change followed by `other`.
    // TODO: make sure to check for sentinel values.
    segment_change combine(const segment_change &other) const {
        if (other.has_set())
            return other;

        return segment_change(to_add + other.to_add, to_set);
    }
};

struct segment {
    ll maximum;
    ll sum;
    ll first, last, max_diff;

    segment(ll _maximum = numeric_limits<ll>::lowest(), ll _sum = 0, ll _first = 0, ll _last = 0,
            ll _max_diff = -1) : maximum(_maximum), sum(_sum), first(_first), last(_last), max_diff(_max_diff) {}

    bool empty() const {
        return max_diff < 0;
    }

    void apply(ll length, const segment_change &change) {
        if (change.has_set()) {
            maximum = change.to_set;
            sum = long(length) * change.to_set;
            first = last = change.to_set;
            max_diff = 0;
        }

        maximum += change.to_add;
        sum += long(length) * change.to_add;
        first += change.to_add;
        last += change.to_add;
    }

    void join(const segment &other) {
        if (empty()) {
            *this = other;
            return;
        } else if (other.empty()) {
            return;
        }

        maximum = max(maximum, other.maximum);
        sum += other.sum;
        max_diff = max({max_diff, other.max_diff, abs(last - other.first)});
        last = other.last;
    }

    void join(const segment &seg0, const segment &seg1) {
        *this = seg0;
        join(seg1);
    }
};

struct seg_tree {
    static ll highest_bit(unsigned x) {return x == 0 ? -1 : 31 - __builtin_clz(x);}

    ll tree_n = 0;
    vector<segment> tree;
    vector<segment_change> changes;

    seg_tree(ll n = -1) {if (n >= 0) init(n);}

    void init(ll n) {
        tree_n = 1;
        while (tree_n < n) tree_n *= 2;
        tree.assign(2 * tree_n, {});
        changes.assign(tree_n, {});
    }

    // Builds our tree from an array in O(n).
    void build(const vector<segment> &initial) {
        ll n = (ll)initial.size();
        init(n);
        copy(initial.begin(), initial.end(), tree.begin() + tree_n);
        for (ll position = tree_n - 1; position > 0; position--) tree[position].join(tree[2 * position], tree[2 * position + 1]);
    }

    void apply_and_combine(ll position, ll length, const segment_change &change) {
        tree[position].apply(length, change);

        if (position < tree_n)
            changes[position] = changes[position].combine(change);
    }

    void push_down(ll position, ll length) {
        if (changes[position].has_change()) {
            apply_and_combine(2 * position, length / 2, changes[position]);
            apply_and_combine(2 * position + 1, length / 2, changes[position]);
            changes[position] = segment_change();
        }
    }

    template<typename T_range_op>
    void process_range(ll position, ll start, ll end, ll a, ll b, bool needs_join, T_range_op &&range_op) {
        if (a <= start && end <= b) {
            range_op(position, end - start);
            return;
        }
        if (position >= tree_n) return;
        push_down(position, end - start);
        ll mid = (start + end) / 2;
        if (a < mid) process_range(2 * position, start, mid, a, b, needs_join, range_op);
        if (b > mid) process_range(2 * position + 1, mid, end, a, b, needs_join, range_op);
        if (needs_join) tree[position].join(tree[2 * position], tree[2 * position + 1]);
    }

    segment query(ll a, ll b) {
        assert(0 <= a && a <= b && b <= tree_n);
        segment answer;
        process_range(1, 0, tree_n, a, b, false, [&](ll position, ll) -> void {answer.join(tree[position]);});
        return answer;
    }

    segment query_full() const {return tree[1];}

    segment query_single(ll index) {
        assert(0 <= index && index < tree_n);
        ll position = tree_n + index;
        for (ll up = highest_bit(tree_n); up > 0; up--) push_down(position >> up, 1 << up);
        return tree[position];
    }

    void update(ll a, ll b, const segment_change &change) {
        assert(0 <= a && a <= b && b <= tree_n);
        process_range(1, 0, tree_n, a, b, true, [&](ll position, ll length) -> void {apply_and_combine(position, length, change);});
    }

    void update_single(ll index, const segment &seg) {
        assert(0 <= index && index < tree_n);
        ll position = tree_n + index;
        for (ll up = highest_bit(tree_n); up > 0; up--) push_down(position >> up, 1 << up);
        tree[position] = seg;
        while (position > 1) position /= 2, tree[position].join(tree[2 * position], tree[2 * position + 1]);
    }

    vector<segment> to_array(ll n) {
        for (ll i = 1; i < tree_n; i++) push_down(i, tree_n >> highest_bit(i));
        return vector<segment>(tree.begin() + tree_n, tree.begin() + tree_n + n);
    }

    // Finds the end of the last subarray starting at `first` satisfying `should_join` via binary search in O(log n).
    template<typename T_bool>
    ll find_last_subarray(T_bool &&should_join, ll n, ll first = 0) {
        assert(0 <= first && first <= n);
        segment current;
        // Check the degenerate case.
        if (!should_join(current, current)) return first - 1;
        return y_combinator([&](auto search, ll position, ll start, ll end) -> ll {
            if (end <= first) return end;
            else if (first <= start && end <= n && should_join(current, tree[position])) {current.join(tree[position]);return end;}
            else if (end - start == 1) {return start;}
            push_down(position, end - start);
            ll mid = (start + end) / 2;
            ll left = search(2 * position, start, mid);
            return left < mid ? left : search(2 * position + 1, mid, end);
        })(1, 0, tree_n);
    }
};

struct segment_tree {
    seg_tree tree;
    ll N;

    segment_tree(ll N) {
        this->N = N;
        tree = seg_tree(N);
        tree.build(vector<segment>(N, segment(0, 0, 0, 0, 0)));
    }

    segment_tree(vector<ll> v) {
        this->N = v.size();
        tree = seg_tree(N);
        tree.build(vector<segment>(N, segment(0, 0, 0, 0, 0)));
        for (ll i = 0; i < N; ++i) tree.update_single(i, segment((ll)v[i], v[i], (ll)v[i], (ll)v[i], 0));
    }

    void p() {
        vector<segment> segs = tree.to_array(N);
        for (ll i = 0; i < N; i++) cout << segs[i].sum << (i < N - 1 ? ' ' : '\n');
    }

    void add(ll a, ll b, ll x) {
        a--;
        assert(0 <= a && a < b && b <= N);
        tree.update(a, b, segment_change((ll)x));
    }

    void set(ll a, ll b, ll x) {
        a--;
        assert(0 <= a && a < b && b <= N);
        if (b - a == 1) tree.update_single(a, segment((ll)x, x, (ll)x, (ll)x, 0));
        else tree.update(a, b, segment_change(0, (ll)x));
    }

    ll max(ll a, ll b) {
        a--;
        assert(0 <= a && a < b && b <= N);
        segment seg = a == 0 && b == N ? tree.query_full() : tree.query(a, b);
        return seg.maximum;
    }

    ll sum(ll a, ll b) {
        a--;
        assert(0 <= a && a < b && b <= N);
        segment seg = a == 0 && b == N ? tree.query_full() : tree.query(a, b);
        return seg.sum;
    }

    ll diff(ll a, ll b) {
        a--;
        assert(0 <= a && a < b && b <= N);
        segment seg = a == 0 && b == N ? tree.query_full() : tree.query(a, b);
        return seg.max_diff;
    }

    //given a, find the first index i with a <= i <= N such that numbers[i] >= x. If no such i exists, print -1.
    ll fmax(ll a, ll x) {
        a--;
        ll index = tree.find_last_subarray([&](const segment &, const segment &add) -> bool {return add.maximum < x;}, N, a);
        return (index < N ? index + 1 : -1);
    }

    //given a, find the first index i with a - 1 <= i <= N such that numbers[a] + ... + numbers[i] is >= x (sum = 0 when i = a - 1). If no such i exists, print -1.
    ll fsum(ll a, ll x) {
        a--;
        ll index = tree.find_last_subarray([&](const segment &current, const segment &add) -> bool {return current.sum + add.sum < x;}, N, a);
        return (index < N ? index + 1 : -1);
    }
};

#define LSOne(S) ((S) & -(S))

class FenwickTree {                              // index 0 is not used
private:
    vector<ll> ft;                                        // internal FT is an array
public:
    FenwickTree(ll m) { ft.assign(m+1, 0); }      // create an empty FT

    void build(const vector<ll> &f) {
        ll m = (ll)f.size()-1;                     // note f[0] is always 0
        ft.assign(m+1, 0);
        for (ll i = 1; i <= m; ++i) {               // O(m)
            ft[i] += f[i];                             // add this value
            if (i+LSOne(i) <= m)                       // i has parent
                ft[i+LSOne(i)] += ft[i];                 // add to that parent
        }
    }

    FenwickTree(const vector<ll> &f) { build(f); }        // create FT based on f

    FenwickTree(ll m, const vector<ll> &s) {              // create FT based on s
        vector<ll> f(m+1, 0);
        for (ll i = 0; i < (ll)s.size(); ++i)      // do the conversion first
            ++f[s[i]];                                 // in O(n)
        build(f);                                    // in O(m)
    }

    ll rsq(ll j) {                                // returns RSQ(1, j)
        ll sum = 0;
        for (; j; j -= LSOne(j))
            sum += ft[j];
        return sum;
    }

    ll rsq(ll i, ll j) { return rsq(j) - rsq(i-1); } // inc/exclusion

    // updates value of the i-th element by v (v can be +ve/inc or -ve/dec)
    void update(ll i, ll v) {
        for (; i < (ll)ft.size(); i += LSOne(i))
            ft[i] += v;
    }

    ll select(ll k) {                             // O(log m)
        ll p = 1;
        while (p*2 < (ll)ft.size()) p *= 2;
        ll i = 0;
        while (p) {
            if (k > ft[i+p]) {
                k -= ft[i+p];
                i += p;
            }
            p /= 2;
        }
        return i+1;
    }
};

class RUPQ {                                     // RUPQ variant
private:
    FenwickTree ft;                                // internally use PURQ FT
public:
    RUPQ(ll m) : ft(FenwickTree(m)) {}
    void range_update(ll ui, ll uj, ll v) {
        ft.update(ui, v);                            // [ui, ui+1, .., m] +v
        ft.update(uj+1, -v);                         // [uj+1, uj+2, .., m] -v
    }                                              // [ui, ui+1, .., uj] +v
    ll point_query(ll i) { return ft.rsq(i); }    // rsq(i) is sufficient
};

class RURQ  {                                    // RURQ variant
private:                                         // needs two helper FTs
    RUPQ rupq;                                     // one RUPQ and
    FenwickTree purq;                              // one PURQ
public:
    RURQ(ll m) : rupq(RUPQ(m)), purq(FenwickTree(m)) {} // initialization
    void range_update(ll ui, ll uj, ll v) {
        rupq.range_update(ui, uj, v);                // [ui, ui+1, .., uj] +v
        purq.update(ui, v*(ui-1));                   // -(ui-1)*v before ui
        purq.update(uj+1, -v*uj);                    // +(uj-ui+1)*v after uj
    }
    ll rsq(ll j) {
        return rupq.point_query(j)*j -               // optimistic calculation
               purq.rsq(j);                          // cancelation factor
    }
    ll rsq(ll i, ll j) { return rsq(j) - rsq(i-1); } // standard
};

class UnionFind {                                // OOP style
private:
    vector<ll> p, rank, setSize;                           // vi p is the key part
    ll numSets;
public:
    UnionFind(ll N) {
        p.assign(N, 0); for (ll i = 0; i < N; ++i) p[i] = i;
        rank.assign(N, 0);                           // optional speedup
        setSize.assign(N, 1);                        // optional feature
        numSets = N;                                 // optional feature
    }
    ll findSet(ll i) { return (p[i] == i) ? i : (p[i] = findSet(p[i])); }
    bool isSameSet(ll i, ll j) { return findSet(i) == findSet(j); }
    void unionSet(ll i, ll j) {
        if (isSameSet(i, j)) return;                 // i and j are in same set
        ll x = findSet(i), y = findSet(j);          // find both rep items
        if (rank[x] > rank[y]) swap(x, y);           // keep x 'shorter' than y
        p[x] = y;                                    // set x under y
        if (rank[x] == rank[y]) ++rank[y];           // optional speedup
        setSize[y] += setSize[x];                    // combine set sizes at y
        --numSets;                                   // a union reduces numSets
    }
    ll numDisjointSets() { return numSets; }
    ll sizeOfSet(ll i) { return setSize[findSet(i)]; }
};

const ll INF = 1e18;                             // large enough

class max_flow {
private:
    ll V;
    map<pair<ll, ll>, ll> is;
    vector< tuple<ll, ll, ll> > EL;
    vector< vector<ll> > AL;
    vector<ll> d, last;
    vector< pair<ll, ll> > p;

    bool BFS(ll s, ll t) {                       // find augmenting path
        d.assign(V, -1); d[s] = 0;
        queue<ll> q({s});
        p.assign(V, {-1, -1});                       // record BFS sp tree
        while (!q.empty()) {
            ll u = q.front(); q.pop();
            if (u == t) break;                         // stop as sink t reached
            for (auto &idx : AL[u]) {                  // explore neighbors of u
                auto &[v, cap, flow] = EL[idx];          // stored in EL[idx]
                if ((cap-flow > 0) && (d[v] == -1))      // positive residual edge
                    d[v] = d[u]+1, q.push(v), p[v] = {u, idx}; // 3 lines in one!
            }
        }
        return d[t] != -1;                           // has an augmenting path
    }

    ll send_one_flow(ll s, ll t, ll f = INF) {   // send one flow from s->t
        if (s == t) return f;                        // bottleneck edge f found
        auto &[u, idx] = p[t];
        auto &cap = get<1>(EL[idx]), &flow = get<2>(EL[idx]);
        ll pushed = send_one_flow(s, u, min(f, cap-flow));
        flow += pushed;
        auto &rflow = get<2>(EL[idx^1]);             // back edge
        rflow -= pushed;                             // back flow
        return pushed;
    }

    ll DFS(ll u, ll t, ll f = INF) {             // traverse from s->t
        if ((u == t) || (f == 0)) return f;
        for (ll &i = last[u]; i < (ll)AL[u].size(); ++i) { // from last edge
            auto &[v, cap, flow] = EL[AL[u][i]];
            if (d[v] != d[u]+1) continue;              // not part of layer graph
            if (ll pushed = DFS(v, t, min(f, cap-flow))) {
                flow += pushed;
                auto &rflow = get<2>(EL[AL[u][i]^1]);     // back edge
                rflow -= pushed;
                return pushed;
            }
        }
        return 0;
    }

public:
    max_flow(ll initialV) : V(initialV) {
        EL.clear();
        AL.assign(V, vector<ll>());
    }

    // if you are adding a bidirectional edge u<->v with weight w into your
    // flow graph, set directed = false (default value is directed = true)
    ll add_edge(ll u, ll v, ll w, bool directed = true) {
        if (u == v) return -1;                          // safeguard: no self loop
        EL.emplace_back(v, w, 0);                    // u->v, cap w, flow 0
        AL[u].push_back(EL.size()-1);                // remember this index
        is[{u, v}] = EL.size() - 1;
        EL.emplace_back(u, directed ? 0 : w, 0);     // back edge
        AL[v].push_back(EL.size()-1);                // remember this index
        return AL[u].back();
    }

    ll edmonds_karp(ll s, ll t) {
        ll mf = 0;                                   // mf stands for max_flow
        while (BFS(s, t)) {                          // an O(V*E^2) algorithm
            ll f = send_one_flow(s, t);                // find and send 1 flow f
            if (f == 0) break;                         // if f == 0, stop
            mf += f;                                   // if f > 0, add to mf
        }
        return mf;
    }

    ll dinic(ll s, ll t) {
        ll mf = 0;                                   // mf stands for max_flow
        while (BFS(s, t)) {                          // an O(V^2*E) algorithm
            last.assign(V, 0);                         // important speedup
            while (ll f = DFS(s, t))                   // exhaust blocking flow
                mf += f;
        }
        return mf;
    }

    set<ll> mincut(ll s, ll t) {
        dinic(s, t);
        set<ll> res;
        queue<ll> q({s});
        vector<bool> vi(n);
        vi[s] = true;
        while (!q.empty()) {
            ll ct = q.front(); q.pop();
            res.insert(ct);
            for (ll i : AL[ct]) {
                auto& [v, c, f] = EL[i];
                if (c > f && !vi[v]) vi[v] = true, q.push(v);
            }
        }
        // edges from one set to another set of nodes
        // for (ll i : res) for (ll j : AL[i]) {
        //     auto& [v, c, f] = EL[j];
        //     if (res.find(v) == res.end() && f > 0) do something with edge
        // }
        return res;
    }

    void debug() {
        for (ll i = 0; i < V; ++i) {
            for (ll j : AL[i]) {
                auto& [v, c, f] = EL[j];
                cout << "From:" << i << " To:" << v << " Cap:" << c << " Flow:" << f << endl;
            }
        }
        cout << "----------MFDEBUG----------\n\n";
    }
};

class min_cost_max_flow {
private:
    ll V;
    ll total_cost;
    vector<tuple<ll, ll, ll, ll>> EL;
    vector< vector<ll> > AL;
    vector<ll> d, last, vis;

    bool SPFA(ll s, ll t) { // SPFA to find augmenting path in residual graph
        d.assign(V, INF); d[s] = 0; vis[s] = 1;
        queue<ll> q({s});
        while (!q.empty()) {
            ll u = q.front(); q.pop(); vis[u] = 0;
            for (auto &idx : AL[u]) {                  // explore neighbors of u
                auto &[v, cap, flow, cost] = EL[idx];          // stored in EL[idx]
                if ((cap-flow > 0) && (d[v] > d[u] + cost)) {      // positive residual edge
                    d[v] = d[u]+cost;
                    if(!vis[v]) q.push(v), vis[v] = 1;
                }
            }
        }
        return d[t] != INF;                           // has an augmenting path
    }

    ll DFS(ll u, ll t, ll f = INF) {             // traverse from s->t
        if ((u == t) || (f == 0)) return f;
        vis[u] = 1;
        for (ll &i = last[u]; i < (ll)AL[u].size(); ++i) { // from last edge
        auto &[v, cap, flow, cost] = EL[AL[u][i]];
        if (!vis[v] && d[v] == d[u]+cost) {                      // in current layer graph
            if (ll pushed = DFS(v, t, min(f, cap-flow))) {
        total_cost += pushed * cost;
            flow += pushed;
            auto &[rv, rcap, rflow, rcost] = EL[AL[u][i]^1]; // back edge
            rflow -= pushed;
            vis[u] = 0;
            return pushed;
            }
        }
        }
        vis[u] = 0;
        return 0;
    }

public:
    min_cost_max_flow(ll initialV) : V(initialV), total_cost(0) {
        EL.clear();
        AL.assign(V, vector<ll>());
        vis.assign(V, 0);
    }

    // if you are adding a bidirectional edge u<->v with weight w into your
    // flow graph, set directed = false (default value is directed = true)
    void add_edge(ll u, ll v, ll w, ll c, bool directed = true) {
        if (u == v) return;                          // safeguard: no self loop
        EL.emplace_back(v, w, 0, c);                 // u->v, cap w, flow 0, cost c
        AL[u].push_back(EL.size()-1);                // remember this index
        EL.emplace_back(u, 0, 0, -c);                // back edge
        AL[v].push_back(EL.size()-1);                // remember this index
        if (!directed) add_edge(v, u, w, c);         // add again in reverse
    }

    pair<ll, ll> mcmf(ll s, ll t) {
        ll mf = 0;                                   // mf stands for max_flow
        while (SPFA(s, t)) {                          // an O(V^2*E) algorithm
            last.assign(V, 0);                         // important speedup
            while (ll f = DFS(s, t))                   // exhaust blocking flow
                mf += f;
        }
        return {mf, total_cost};
    }

    void debug() {
        for (ll i = 0; i < V; ++i) {
            for (ll j : AL[i]) {
                auto& [v, c, f, h] = EL[j];
                cout << "From:" << i << " To:" << v << " Cap:" << c << " Flow:" << f << " Cost:" << h << endl;
            }
        }
        cout << "----------MFDEBUG----------\n\n";
    }
};

struct hungarian {
private:
    //internally 1 indexed
    bool flipped = false; //if n > m, n and m will switch
    ll n, m;
    vector< vector<ll> > A; //cost matrix, can change to ld for real numbers
    vector<ll> u, v; //stores potential, can change to ld for real numbers
    vector<ll> p; //contains matchings for index 1 to m
    vector<ll> way; //number of previous column in augmenting path
    vector< pair<ll, ll> > res; //result of pairs of matching
public:
    hungarian(ll n, ll m) {
        if (n > m) {
            flipped = true;
            ll temp = n;
            n = m;
            m = temp;
        }
        this->n = n, this->m = m;
        A = vector< vector<ll> >(n + 1, vector<ll>(m + 1)); //can change to ld
        u = vector<ll>(n + 1); //can change to ld
        v = vector<ll>(m + 1); //can change to ld
        p = vector<ll>(m + 1);
        way = vector<ll>(m + 1);
    }

    void add_edge(ll u, ll v, ll c) { //can change c to ld
        if (flipped) A[v + 1][u + 1] = c;
        else A[u + 1][v + 1] = c;
    }

    pair<ll, ll> solve() {
        for (ll i = 1; i <= n; ++i) {
            p[0] = i;
            ll j0 = 0;
            vector<ll> minv (m + 1, INF);
            vector<bool> used (m + 1, false);
            do {
                used[j0] = true;
                ll i0 = p[j0], delta = INF, j1;
                for (ll j = 1; j <= m; ++j)
                    if (!used[j]) {
                        ll cur = A[i0][j]-u[i0]-v[j];
                        if (cur < minv[j])
                            minv[j] = cur,  way[j] = j0;
                        if (minv[j] < delta)
                            delta = minv[j],  j1 = j;
                    }
                for (ll j = 0; j <= m; ++j)
                    if (used[j])
                        u[p[j]] += delta,  v[j] -= delta;
                    else
                        minv[j] -= delta;
                j0 = j1;
            } while (p[j0] != 0);
            do {
                ll j1 = way[j0];
                p[j0] = p[j1];
                j0 = j1;
            } while (j0);
        }
        for (ll i = 1; i <= m; ++i) if (p[i]) res.emplace_back(p[i], i);
        return {-v[0], res.size()}; //by default min cost, remove negative for max
    }

    void print() {
        for (auto& [a, b] : res) {
            if (flipped) cout << b << " " << a << endl;
            else cout << a << " " << b << endl;
        }
    }
};

struct MCBM {
private:
    vector<ll> match, vis;
    vector< vector<ll> > AL;
    ll V;
public:
    MCBM(ll V) {
        this->V = V;
        AL.assign(V, {});
    }

    void add_edge(ll i, ll j) {
        AL[i].push_back(j);
    }

    ll Aug(ll L) {
        if (vis[L]) return 0;                          // L visited, return 0
        vis[L] = 1;
        for (auto &R : AL[L]) if ((match[R] == -1) || Aug(match[R])) {
            match[R] = L;                              // flip status
            return 1;                                  // found 1 matching
        }
        return 0;                                      // no matching
    }

    ll result(ll Vleft) {
        unordered_set<ll> freeV;
        for (ll L = 0; L < Vleft; ++L) freeV.insert(L);// initial assumption
        match.assign(V, -1);
        ll MCBM = 0;
        // Greedy pre-processing for trivial Augmenting Paths
        // try commenting versus un-commenting this for-loop
        for (ll L = 0; L < Vleft; ++L) {              // O(V+E)
            vector<ll> candidates;
            for (auto &R : AL[L]) if (match[R] == -1) candidates.push_back(R);
            if ((ll) candidates.size() > 0) {
              ++MCBM;
              freeV.erase(L);                          // L is matched
              ll a = rand()%(ll)candidates.size();     // randomize this
              match[candidates[a]] = L;
            }
        }                                              // for each free vertex
        for (auto &f : freeV) {                        // (in random order)
            vis.assign(Vleft, 0);                      // reset first
            MCBM += Aug(f);                            // try to match f
        }
        return MCBM;
    }

    vector<ll> matches(ll L) {
        vector<ll> res(n);
        for (ll i = L; i < V; ++i) if(match[i] != -1) res[match[i]] = i - L;
        return res;
    }
};

// Count number of primes
uint64_t root(uint64_t a, ll k) {
    if(a <= 1 || k == 1) { return a; }
    if(k >= 64) { return 1; }
    auto check = [&](__uint128_t n) {
        __uint128_t x = 1, m = n;
        for(ll p = k; p; p >>= 1, m *= m) {
            if(p & 1) { x *= m; }
        }
        return x <= a;
    };
    uint64_t n = powl(a, (long double)(1.0) / k);
    while(!check(n)) { --n; }
    while(check(n + 1)) { ++n; }
    return n;
}

vector<bool> Eratosthenes(ll n) {
    vector<bool> prime(n + 1, true);
    if(n >= 0) { prime[0] = false; }
    if(n >= 1) { prime[1] = false; }
    for(ll i = 2; i * i <= n; i++) {
        if(!prime[i]) { continue; }
        for(ll j = i + i; j <= n; j += i) { prime[j] = false; }
    }
    return prime;
}

struct PrimeCount {
private:
    ll p2(ll x, ll y) {
        if(x < 4) { return 0; }
        ll a = cnt(y), b = cnt(root(x, 2));
        if(a >= b) { return 0; }
        ll sum = (a - 2) * (a + 1) / 2 - (b - 2) * (b + 1) / 2;
        for(ll i = a; i < b; i++) { sum += cnt(x / primes[i]); }
        return sum;
    }
    ll phi(ll m, ll n) {
        if(m < 1) { return 0; }
        if(n > m) { return 1; }
        if(n < 1) { return m; }
        if(m <= primes[n - 1] * primes[n - 1]) { return cnt(m) - n + 1; }
        if(m <= primes[n - 1] * primes[n - 1] * primes[n - 1] && m <= sq) {
            ll sx = cnt(root(m, 2)), ans = cnt(m) - (sx + n - 2) * (sx - n + 1) / 2;
            for(ll i = n; i < sx; i++) { ans += cnt(m / primes[i]); }
            return ans;
        }
        return phi(m, n - 1) - phi(m / primes[n - 1], n - 1);
    }

public:
    ll sq;
    vector<bool> prime;
    vector<ll> prime_sum, primes;
    PrimeCount(ll n): sq(root(n, 2)), prime_sum(sq + 1) {
        prime = Eratosthenes(sq);
        for(ll i = 1; i <= sq; i++) { prime_sum[i] = prime_sum[i - 1] + prime[i]; }
        primes.reserve(prime_sum[sq]);
        for(ll i = 1; i <= sq; i++) {
            if(prime[i]) { primes.emplace_back(i); }
        }
    }
    ll cnt(ll n) {
        if(n <= sq) { return prime_sum[n]; }
        ll m = root(n, 3), a = cnt(m);
        return phi(n, a) + a - 1 - p2(n, m);
    }
    inline ll operator()(ll n) { return cnt(n); }
};

// remember change this when have other characters
template<char MIN_CHAR = 'a', ll ALPHABET = 26>
struct array_trie {
    struct trie_node {
        array<ll, ALPHABET> child;
        ll words_here = 0, starting_with = 0;

        trie_node() {
            memset(&child[0], -1, ALPHABET * sizeof(ll));
        }
    };

    static const ll ROOT = 0;

    vector<trie_node> nodes = {trie_node()};

    array_trie(ll total_length = -1) {
        if (total_length >= 0)
            nodes.reserve(total_length + 1);
    }

    ll get_or_create_child(ll node, ll c) {
        if (nodes[node].child[c] < 0) {
            nodes[node].child[c] = ll(nodes.size());
            nodes.emplace_back();
        }

        return nodes[node].child[c];
    }

    ll build(const string &word, ll delta) {
        ll node = ROOT;

        for (char ch : word) {
            nodes[node].starting_with += delta;
            node = get_or_create_child(node, ch - MIN_CHAR);
        }

        nodes[node].starting_with += delta;
        return node;
    }

    ll add(const string &word) {
        ll node = build(word, +1);
        nodes[node].words_here++;
        return node;
    }

    ll erase(const string &word) {
        ll node = build(word, -1);
        nodes[node].words_here--;
        return node;
    }

    ll find(const string &str) const {
        ll node = ROOT;

        for (char ch : str) {
            node = nodes[node].child[ch - MIN_CHAR];

            if (node < 0)
                break;
        }

        return node;
    }

    // Given a string, how many words in the trie are prefixes of the string?
    ll count_prefixes(const string &str, bool include_full) const {
        ll node = ROOT, count = 0;

        for (char ch : str) {
            count += nodes[node].words_here;
            node = nodes[node].child[ch - MIN_CHAR];

            if (node < 0)
                break;
        }

        if (include_full && node >= 0)
            count += nodes[node].words_here;

        return count;
    }

    // Given a string, how many words in the trie start with the given string?
    ll count_starting_with(const string &str, bool include_full) const {
        ll node = find(str);

        if (node < 0)
            return 0;

        return nodes[node].starting_with - (include_full ? 0 : nodes[node].words_here);
    }
};

struct pprime {
private:
    ll binpower(ll base, ll e, ll mod) {
        ll result = 1;
        base %= mod;
        while (e) {
            if (e & 1) result = (ll) result * base % mod;
            base = (ll) base * base % mod;
            e >>= 1;
        }
        return result;
    }

    bool check_composite(ll n, ll a, ll d, int s) {
        ll x = binpower(a, d, n);
        if (x == 1 || x == n - 1)
            return false;
        for (ll r = 1; r < s; r++) {
            x = (ll) x * x % n;
            if (x == n - 1) return false;
        }
        return true;
    };

public:
    bool isProbablePrime(ll n, ll iter = 10) { //Miller-Rabin
        if (n < 4) return n == 2 || n == 3;
        ll s = 0;
        ll d = n - 1;
        while ((d & 1) == 0) d >>= 1, s++;
        for (ll i = 0; i < iter; i++) {
            ll a = 2 + rand() % (n - 3);
            if (check_composite(n, a, d, s)) return false;
        }
        return true;
    }
};