#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cstdint>
#include <cassert>
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
  set<const robdd*,pointer_cmp<robdd>> cache;
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
  map<pair<const robdd*,const robdd*>, const robdd*> and_cache;
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
  map<pair<const robdd*,const robdd*>, const robdd*> or_cache;
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
  map<const robdd*, const robdd*> subset_cache;
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
  map<const robdd*, const robdd*> supset_cache;
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
  map<const robdd*, const robdd*> conj_cache;
  const robdd* conj(const robdd* arg) {
    // (t,f) -> (t or f,f)
    if (arg==TRUE) return FALSE;
    if (arg==FALSE) return TRUE;
    auto it = conj_cache.find(arg);
    if (it != conj_cache.end()) return it->second;
    const robdd *r = robdd(arg->layer, conj(arg->one), conj(arg->zero)).intern();
    conj_cache[arg] = r;
    return r;
  }
}

namespace param {
  const int n=4;
  const int w=2;
  const int d=3;
}

bool check(const robdd::robdd* r, int s) {
  if (r==robdd::FALSE) return false;
  if (r==robdd::TRUE) return true;
  return check((s&(1<<r->layer))?r->one:r->zero, s);
}

const robdd::robdd* construct(int s) {
  const robdd::robdd* r=robdd::TRUE;
  for (int i=param::n-1; i>=0; i--) {
    if (s&(1<<i)) 
      r = robdd::robdd(i, r, robdd::FALSE).intern();
    else
      r = robdd::robdd(i, robdd::FALSE, r).intern();
  }
  return r;
}

struct enumerate {
  vector<int> result;
  void search(const robdd::robdd * c, int depth, int value, int pop) {
    if (pop > param::d) return;
    if (c == robdd::FALSE) return;
    if (c == robdd::TRUE?param::n:c->layer > depth) {
      search(c, depth+1, value, pop);
      search(c, depth+1, value | (1<<depth), pop + 1);
    } else if (c == robdd::TRUE) {
      result.push_back(value);
    } else {
      assert(c->layer == depth);
      search(c->zero, depth+1, value, pop);
      search(c->one,  depth+1, value | (1<<depth), pop + 1);
    }
  }
  enumerate(const robdd::robdd * c) {
    search(c,0,0,0);
  }
};
  
struct sequence {
  const robdd::robdd * forbidden;
  const robdd::robdd * prev;
  sequence * tail;
  int length;
  int refs;
  
  sequence() : forbidden(robdd::FALSE), prev(robdd::FALSE), tail(NULL), length(0), refs(0) {}
  sequence(sequence * tail, const robdd::robdd * next) : 
    forbidden(robdd::Or(tail->forbidden,robdd::Or(next, robdd::supset(robdd::And(robdd::subset(tail->prev), robdd::conj(next)))))), 
    prev(next), 
    tail(tail), length(tail->length+1), refs(0) {}
  ~sequence() {
    if (tail && --tail->refs) delete tail;
  }
  bool operator<(const sequence &b) const {
    if (forbidden == b.forbidden) {
      return prev < b.prev;
    }
    return forbidden < b.forbidden;
  }
};

const static char symbols[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
ostream& operator<<(ostream& o, const sequence &s) {
  if (s.tail) {
    o << *s.tail << " ";
  }
  o << "{";
  bool not_first = false;
  for (int i : enumerate(s.prev).result) {
    if (not_first) o << ",";
    not_first = true;
    for (int j=0; j<param::n; j++) {
      if (i & (1<<j)) {
        o << symbols[j];
      }
    }
  }
  o << "}";
  return o;
}

static set<sequence*,pointer_cmp<sequence>> cur, nxt;
static sequence * seq;
void generate_next(const vector<const robdd::robdd *> &old_compatible, const robdd::robdd * old_next, const robdd::robdd * not_anti, int depth) {
  vector<const robdd::robdd *> compatible;
  for (const robdd::robdd * c : old_compatible) {
    if (robdd::And(not_anti, c) != robdd::FALSE) continue; // Skip those elements that would violate the anti-chain.
    const robdd::robdd * next = robdd::Or(old_next, c); // Compute the new next set
    sequence * x = new sequence(seq, next); // Create new sequence
    if (nxt.empty()) { // Print if the first
      cout << "n=" << param::n << " |F_i|<=" << param::w << " d=" << param::d << " t=" << x->length << ": " << *x << endl;
    }
    nxt.insert(x); // Insert into the nxt set
    if (depth < param::w) { // If still allowed, recurse
      generate_next(compatible, next, robdd::Or(not_anti,robdd::Or(robdd::subset(c),robdd::supset(c))), depth+1);
    }
    compatible.push_back(c); // Track elements that can be chosen in a recursive call
  }
};

int main(int argc, const char *argv[]) {
  sequence* root = new sequence;
  for (int i=0; i<param::n; i++) {
    cur.insert(new sequence(root, construct((2<<i)-1)));
  }
  while (!cur.empty()) {
    for (sequence * s : cur) {
      seq = s;
      vector<const robdd::robdd *> compatible;
      for (int i : enumerate(robdd::conj(seq->forbidden)).result) {
        compatible.push_back(construct(i));
      }
      generate_next(compatible, robdd::FALSE, robdd::FALSE, 1);
      if (seq->refs == 0) delete s;
    }
    swap(cur,nxt);
    nxt.clear();
  }
  return 0;
}