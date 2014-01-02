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

const int n=6;
const int w=2;
const int d=2;

const int set_count = 1<<n;

uint64_t hash_value(uint64_t x) {
  x ^= x<<13;
  x ^= x<<29;
  return (x * (x * x * 15731 + 789221) + 1376312589) * 1234567891;
}

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

ostream& operator<<(ostream& o, const sequence &s) {
  if (s.tail) {
    o << *s.tail << ",";
  }
  o << "{";
  for (int i=0; i<w; i++) {
    if (s.prev[i]!=0) {
      if (i>0) o << ",";
      bool not_first = false;
      o << "{";
      for (int j=0; j<n; j++) {
        if (s.prev[i] & (1<<j)) {
          if (not_first) {
            o << ",";
          }
          not_first = true;
          o << j;
        }
      }
      o << "}";
    }
  }
  o << "}";
  return o;
}

struct seq_cmp {
  inline bool operator()(const sequence *a, const sequence *b) {
    return *a < *b;
  }
};

static bool shown = false;
static vector<int> compatible;
static set<sequence*,seq_cmp> cur, nxt;

void generate_next(sequence * s, int next[w], int index, int start) {
  for (uint i=start; i < compatible.size(); i++) {
    next[index] = compatible[i];
    for (int j=0; j<index; j++) {
      // anti-chain check
      if ((next[index] & ~next[j])==0 || (~next[index] & next[j])==0) goto failure;
    }
    /* else */
    {
      sequence * x = new sequence(s, next);
      if (!shown) {
        cout << "n=" << n << " |F_i|<=" << w << " d=" << d << " t=" << x->length << ": " << *x << endl;
        shown = true;
      }
      nxt.insert(x);
      if (index+1<w) {
        generate_next(s, next, index+1, i+1);
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
          int new_used = s->used | T;
          if ((new_used & (new_used+1)) != 0) continue;
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
        generate_next(s, next, 0, 0);

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