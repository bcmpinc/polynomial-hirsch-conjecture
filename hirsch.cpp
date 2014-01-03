#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <string>
#include <iostream>
#include <algorithm>
#include <vector>
#include <queue>
#include <list>
#include <stack>
#include <map>
#include <set>

/** Definition 1: sequence
 * A sequence is F_1,...,F_t subset powerset({0,...,n-1}), with 
 * F_1,...,F_t disjoint and
 * forall i: 1 <= i <= t: emptyset not in F_i and F_i non empty.
 */

/** Definition 2: f(n)
 * f(n) is defined as the longest sequence for the given value of n.
 */

/** Definition 3: convexity
 * A sequence F_1,...,F_t is convex iff forall i < j < k: forall R in F_i, T in F_k: exists S in F_j: R intersect T subset S.
 */

/** Lemma 1: chain length invariant
 * F_1,...,F_t is convex iff F_1,...,F_t-1 is convex and union(F_1,..,F_t-2),F_t-1,F_t is convex.
 * Proof: => is trivial as these are subsequences, so we only proof <=.
 * For k < t convexity is given, so assume T in F_t.
 * Let i,j and R in F_i be given. 
 * R in union(F_1,..,F_2-2), hence convexity gives a T' in F_t-1, with R intersect T subset T'.
 * If j=t-1 were done, otherwise convexity gives a S in F_j with R intersect T' subset S.
 * Now, R intersect T subset of R intersect T' subset S. QED
 */

/** Lemma 2: size of F_1
 * |F_1| = 1.
 * Proof: Elements can be removed from F_1 without affecting convexity or t. QED
 */

/** Lemma 3: intervals
 * F_1,...,F_t is convex iff (forall a subset {0,..,n-1}: exist i,k: i <= k: forall j : (i <= j <= k) iff (exist S in F_j: a in S)).
 * Proof: => is implied by convexity. So we now proof <=.
 * Assume we have a sequence that has the interval property but is not convex.
 * Then there is an S: S subset R in F_i and S subset T in F_k, but S not subset F_j and thus the interval of S has a hole. 
 * This leads to a contradiction. QED
 */

/** Conjecture 1: fixed F_1
 * F_1 = {{0}}
 */

using namespace std;

template<class T>
struct pointer_cmp {
  inline bool operator()(const T *a, const T *b) {
    return *a < *b;
  }
};

namespace robdd {
  struct robdd;
  std::set<const robdd*,pointer_cmp<robdd>> cache;
  struct robdd {
    int layer;
    const robdd *one, *zero; // These pointers are required to be in the cache.
    robdd() : layer(-1), one(NULL), zero(NULL) {};
    robdd(int layer, const robdd *one, const robdd *zero) : layer(layer), one(one), zero(zero) {}
    const robdd* intern() const {
      // Returns a cached version of this robdd.
      if (one == zero) return one;
      auto it = cache.find(this);
      if (it != cache.end()) return *it;
      robdd * r = new robdd(*this);
      cache.insert(r);
      return r;
    }
    bool operator<(const robdd& b) const {
      return memcmp(this, &b, sizeof(robdd)) < 0;
    }
  };

  const robdd* FALSE((robdd*)0);
  const robdd* TRUE((robdd*)1);
  std::map<std::pair<const robdd*,const robdd*>, const robdd*> and_cache;
  const robdd* And(const robdd *a, const robdd *b) {
    // Shortcuts
    if (a==FALSE || b==FALSE) return FALSE;
    if (a==TRUE) return b;
    if (b==TRUE) return a;
    if (a>b) swap(a,b); // Remove element order from pair.
    auto it = and_cache.find(make_pair(a,b));
    if (it != and_cache.end()) return it->second;
    // Merge
    const robdd *r;
    if (a->layer<b->layer) r = robdd(a->layer,And(a->one,b),And(a->zero,b)).intern(); else
    if (a->layer>b->layer) r = robdd(b->layer,And(a,b->one),And(a,b->zero)).intern(); else
    r = robdd(a->layer,And(a->one,b->one),And(a->zero,b->zero)).intern();
    and_cache[make_pair(a,b)] = r;
    return r;
  }
  std::map<std::pair<const robdd*,const robdd*>, const robdd*> or_cache;
  const robdd* Or(const robdd *a, const robdd *b) {
    // Shortcuts
    if (a==TRUE || b==TRUE) return TRUE;
    if (a==FALSE) return b;
    if (b==FALSE) return a;
    if (a>b) swap(a,b); // Remove element order from pair.
    auto it = or_cache.find(make_pair(a,b));
    if (it != or_cache.end()) return it->second;
    // Merge
    const robdd *r;
    if (a->layer<b->layer) r = robdd(a->layer,Or(a->one,b),Or(a->zero,b)).intern(); else
    if (a->layer>b->layer) r = robdd(b->layer,Or(a,b->one),Or(a,b->zero)).intern(); else
    r = robdd(a->layer,Or(a->one,b->one),Or(a->zero,b->zero)).intern();
    or_cache[make_pair(a,b)] = r;
    return r;
  }
  std::map<const robdd*, const robdd*> subset_cache;
  const robdd* subset(const robdd* arg) {
    // (t,f) -> (t,t or f)
    if (arg==TRUE || arg==FALSE) return arg;
    auto it = subset_cache.find(arg);
    if (it != subset_cache.end()) return it->second;
    const robdd *r;
    r = subset(arg->one);
    r = robdd(arg->layer, r,Or(r,subset(arg->zero))).intern();
    subset_cache[arg] = r;
    return r;
  }
  std::map<const robdd*, const robdd*> supset_cache;
  const robdd* supset(const robdd* arg) {
    // (t,f) -> (t or f,f)
    if (arg==TRUE || arg==FALSE) return arg;
    auto it = subset_cache.find(arg);
    if (it != subset_cache.end()) return it->second;
    const robdd *r;
    r = supset(arg->zero);
    r = robdd(arg->layer, Or(supset(arg->one), r), r).intern();
    supset_cache[arg] = r;
    return r;
  }
}

const int n=5;
const int w=2;
const int d=3;

bool check(const robdd::robdd* r, int s) {
  if (r==robdd::FALSE) return false;
  if (r==robdd::TRUE) return true;
  return check((s&(1<<r->layer))?r->one:r->zero, s);
}

const robdd::robdd* construct(int s) {
  const robdd::robdd* r=robdd::TRUE;
  for (int i=w-1; i>=0; i--) {
    if (s&(1<<i)) 
      r = robdd::robdd(i, r, robdd::FALSE).intern();
    else
      r = robdd::robdd(i, robdd::FALSE, r).intern();
  }
  return r;
}

uint64_t hash_value(uint64_t x) {
  x ^= x<<13;
  x ^= x<<29;
  return (x * (x * x * 15731 + 789221) + 1376312589) * 1234567891;
}

const int set_count = 1<<n;

const int uint64_t_bits = sizeof(uint64_t)*8;
const int base_count = (set_count + uint64_t_bits - 1) / uint64_t_bits;

void set_bit(uint64_t * bitmap, int index) {
  bitmap[index/uint64_t_bits] |= (1ULL<<(index%uint64_t_bits));
}

bool get_bit(uint64_t * bitmap, int index) {
  return bitmap[index/uint64_t_bits] & (1ULL<<(index%uint64_t_bits));
}

struct sequence {
  uint64_t base[base_count];
  int prev[w];
  uint64_t hash;
  int length;
  sequence * tail;
  int refs;
  int used;
  
  sequence() {
    for(uint i=0; i<base_count; i++) base[i]=false;
    for(int i=0; i<w; i++) prev[i]=0;
    tail = NULL;
    length = 0;
    refs = 0;
    hash = 0;
    used = 0;
  }
  sequence(sequence * le_tail, int next[w]) {
    memcpy(this, le_tail, sizeof(sequence));
    tail = le_tail;
    tail->refs++;
    length++;
    refs = 0;
    for(int i=0; i<w; i++) {
      hash ^= hash_value(prev[i]);
      set_bit(base, prev[i]);
      prev[i]=next[i];
      used |= next[i];
    }
  }
  ~sequence() {
    if (tail) {
      tail->refs--;
      if (tail->refs<=0) delete tail;
    }
  }
  bool operator<(const sequence &b) const {
    if (hash == b.hash) {
      int i = memcmp(prev, b.prev, sizeof(prev));
      if (i==0) {
        i = memcmp(base, b.base, sizeof(base));
        return i<0;
      }
      return i<0;
    }
    return hash < b.hash;
  }
};

const static char symbols[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
ostream& operator<<(ostream& o, const sequence &s) {
  if (s.tail) {
    o << *s.tail << " ";
  }
  o << "{";
  for (int i=0; i<w; i++) {
    if (s.prev[i]!=0) {
      if (i>0) o << ",";
      for (int j=0; j<n; j++) {
        if (s.prev[i] & (1<<j)) {
          o << symbols[j];
        }
      }
    }
  }
  o << "}";
  return o;
}

static bool shown = false;
static vector<int> compatible;
static set<sequence*,pointer_cmp<sequence>> cur, nxt;

void generate_next(sequence * s, int next[w], int index, int start, int used) {
  for (uint i=start; i < compatible.size(); i++) {
    next[index] = compatible[i];
    for (int j=0; j<index; j++) {
      // anti-chain check
      if ((next[index] & ~next[j])==0 || (~next[index] & next[j])==0) goto failure;
    }
    /* else */
    {
      // Symmetry breaking on which numbers are introduced.
      int mask = used | next[index];
      if ((mask & (mask+1)) == 0) {
        sequence * x = new sequence(s, next);
        if (!shown) {
          cout << "n=" << n << " |F_i|<=" << w << " d=" << d << " t=" << x->length << ": " << *x << endl;
          shown = true;
        }
        nxt.insert(x);
      }
      if (index+1<w) {
        generate_next(s, next, index+1, i+1, used | next[index]);
      }
    }
    failure:;
  }
  next[index]=0;
};

int main(int argc, const char *argv[]) {
  for (int i=0; i<1; i++) {
    {
      sequence *s=new sequence();
      s->prev[0] = (2<<i) - 1;
      s->used |= s->prev[0];
      s->length = 1;
      cur.insert(s);
    }
    while (!cur.empty()) {
      shown = false;
      for (sequence* s : cur) {
        compatible.clear();
        
        // Compute compatible subsets
        for (int T=1; T<set_count; T++) {
          if (__builtin_popcount(T)>d) continue;
          if (get_bit(s->base, T)) continue;
          for (int i=0; i<w; i++) if (s->prev[i] == T) goto failure;
          for (int i=0; i<base_count; i++) {
            uint64_t m = s->base[i];
            while (m) {
              int R = __builtin_ctzll(m) + uint64_t_bits * i;
              m &= m-1;
              int j=0;
              while (j<w && (R & T & ~s->prev[j])) j++;
              if (j==w) goto failure;
            }
          }
          compatible.push_back(T);
          failure:;
        }
        
        int next[w];
        for (int j=0; j<w; j++) next[j]=0;
        generate_next(s, next, 0, 0, s->used);

        if (s->refs == 0) {
          delete s;
        }
      }
      swap(cur,nxt);
      nxt.clear();
    }
  }
  return 0;
}