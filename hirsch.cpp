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

using namespace std;

//#define NDEBUG
namespace param {
  const int n=6;
  const int w=2;
  const int d=n;
}

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

template<class T>
struct pointer_cmp {
  inline bool operator()(const T *a, const T *b) {
    assert(a);
    assert(b);
    return *a < *b;
  }
};
template<class T>
struct index_cmp {
  const T* array;
  index_cmp(const T* array) : array(array) {}
  inline bool operator()(int a, int b) {
    return array[a] < array[b];
  }
};

namespace robdd {
  struct robdd;
  set<const robdd*,pointer_cmp<robdd>> cache;
  struct robdd {
    const robdd *one, *zero; // These pointers are required to be in the cache.
    int layer;
    robdd() : one(NULL), zero(NULL), layer(-1) {};
    robdd(int layer, const robdd *one, const robdd *zero) : one(one), zero(zero), layer(layer) {}
    const robdd* intern() const {
      // Returns a cached version of this robdd.
      if (one == zero) return one;
      auto it = cache.find(this);
      if (it != cache.end()) return *it;
      robdd * r = new robdd(*this);
      bool added = cache.insert(r).second;
      assert(added);
      return r;
    }
    bool operator<(const robdd& b) const {
      if (one != b.one) return one < b.one;
      if (zero != b.zero) return zero < b.zero;
      return layer < b.layer;
    }
  };
  void clear_cache() {for (const robdd* r : cache) delete r; cache.clear();}

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
    auto it = supset_cache.find(arg);
    if (it != supset_cache.end()) return it->second;
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
  map<const robdd*, pair<int, int>> sat_count_cache;
  pair<int, int> sat_count(const robdd* arg) {
    if (arg==TRUE) return make_pair(1,param::n);
    if (arg==FALSE) return make_pair(0,param::n);
    auto it = sat_count_cache.find(arg);
    if (it != sat_count_cache.end()) return it->second;
    auto cnt_one  = sat_count(arg->one);
    auto cnt_zero = sat_count(arg->zero);
    auto r = make_pair((cnt_one.first<<(cnt_one.second-arg->layer-1))+(cnt_zero.first<<(cnt_zero.second-arg->layer-1)),arg->layer);
    sat_count_cache[arg] = r;
    return r;
  }
  struct permutator {
    int var[param::n];
    map<const robdd*, const robdd*> permute_cache;
    permutator() {for (int i=0; i<param::n; i++) var[i]=i;}
    template<class T>
    void sort(T* sort_key) {std::sort(var,var+param::n,index_cmp<T>(sort_key));}
    const robdd* permute(const robdd* org, int index) {
      if (org==TRUE) return TRUE;
      if (org==FALSE) return FALSE;
      if (index>=param::n) return TRUE;
      auto it = permute_cache.find(org);
      if (it != permute_cache.end()) return it->second;
      const robdd* r = robdd(index,
        permute(And(robdd(var[index],TRUE,FALSE).intern(), org), index+1),
        permute(And(robdd(var[index],FALSE,TRUE).intern(), org), index+1)
      ).intern();
      permute_cache[org] = r;
      return r;
    }
  };
  int get_element(const robdd* c) {
    if (c==FALSE) return -1;
    int r=0;
    while (c!=TRUE) {
      assert(c!=FALSE);
      if (c->zero != FALSE) {
        c = c->zero;
      } else {
        r += 1<<(param::n-c->layer-1);
        c = c->one;
      }
    }
    return r;
  }
  int get_non_element(const robdd* c) {
    if (c==FALSE) return -1;
    int r=0;
    while (c!=TRUE) {
      assert(c!=FALSE);
      if (c->zero != FALSE) {
        r += 1<<(param::n-c->layer-1);
        c = c->zero;
      } else {
        c = c->one;
      }
    }
    return r;
  }
  map<const robdd*, const robdd*> canonicalize_cache;
  const robdd* canonicalize(const robdd* arg) {
    if (arg==TRUE || arg==FALSE) return arg;
    auto it = canonicalize_cache.find(arg);
    if (it != canonicalize_cache.end()) return it->second;
    typedef tuple<int,int,int,int> KEY;
    KEY sort_key[param::n];
    // Compute permutation
    for (int i=0; i<param::n; i++) {
      const robdd * v = And(arg, robdd(i,TRUE,FALSE).intern());
      auto count = sat_count(v);
      sort_key[i] = KEY(count.first << count.second, get_non_element(v), get_element(v), i);
    }
    permutator perm;
    perm.sort(sort_key);
    // Compute result
    const robdd* r = perm.permute(arg, 0);
    canonicalize_cache[arg] = r;
    return r;
  }
  const robdd* remove_layer(const robdd* arg, int layer) {
    if (arg==TRUE || arg==FALSE || arg->layer>layer) return arg;
    if (arg->layer == layer) return Or(arg->one, arg->zero);
    return robdd(arg->layer, remove_layer(arg->one,layer), remove_layer(arg->zero,layer)).intern();
  }
  struct sat_info {
    int count[param::n+1];
    bool operator<(const sat_info &b) const {return memcmp(count, b.count, sizeof(count))<0;}
  };
  map<const robdd*, sat_info> info_cache;
  const sat_info& info(const robdd* arg) {
    auto it = info_cache.find(arg);
    if (it != info_cache.end()) return it->second;
    sat_info &r = info_cache[arg];
    for (int i=0; i<param::n; i++) {
      const robdd * v = And(arg, robdd(i,TRUE,FALSE).intern());
      auto c = sat_count(v);
      r.count[i] = c.first<<c.second;
    }
    auto c = sat_count(arg);
    sort(r.count, r.count+param::n);
    r.count[param::n] = c.first<<c.second;
    return r;
  }
}

bool check(const robdd::robdd* r, int s) {
  if (r==robdd::FALSE) return false;
  if (r==robdd::TRUE) return true;
  return check((s&(1<<r->layer))?r->one:r->zero, s);
}

static const robdd::robdd * precomputed_subset[1<<param::n];
const robdd::robdd * construct(int s) {
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
    if ((c == robdd::TRUE?param::n:c->layer) > depth) {
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
  
  sequence() : forbidden(precomputed_subset[0]), prev(forbidden), tail(NULL), length(0), refs(1) {}
  sequence(sequence * tail, const robdd::robdd * next) : 
    forbidden(robdd::Or(tail->forbidden,robdd::Or(next, robdd::supset(robdd::And(robdd::subset(tail->prev), robdd::conj(robdd::subset(next))))))), 
    prev(next), 
    tail(tail), length(tail->length+1), refs(1) {tail->ref();}
  ~sequence() {
    if (tail) tail->unref();
  }
  void ref() {++refs;}
  void unref() {if(--refs==0) delete this;}
  bool operator<(const sequence &b) const {
    /*if (forbidden == b.forbidden) {
      return prev < b.prev;
    }*/
    return robdd::info(forbidden) < robdd::info(b.forbidden);
  }
};

const static char symbols[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
ostream& operator<<(ostream& o, const enumerate &e) {
  o << "{";
  bool not_first = false;
  for (int i : e.result) {
    if (not_first) o << ",";
    not_first = true;
    if (i==0) o << "-"; else
    for (int j=0; j<param::n; j++) {
      if (i & (1<<j)) {
        o << symbols[j];
      }
    }
  }
  o << "}";
  return o;
}
ostream& operator<<(ostream& o, const sequence &s) {
  if (s.tail) {
    o << *s.tail << " ";
  }
  return o << enumerate(s.prev);
}

static set<sequence*,pointer_cmp<sequence>> cur, nxt;
static sequence * seq;
void generate_next(const vector<const robdd::robdd *> &old_compatible, const robdd::robdd * old_next, const robdd::robdd * not_anti, int depth) {
  vector<const robdd::robdd *> compatible;
  for (const robdd::robdd * c : old_compatible) {
    if (robdd::And(not_anti, c) != robdd::FALSE) continue; // Skip those elements that would violate the anti-chain.
    const robdd::robdd * next = robdd::Or(old_next, c); // Compute the new next set
    sequence * x = new sequence(seq, next); // Create new sequence
    assert(robdd::And(x->forbidden, next) == next);
    if (nxt.empty()) { // Print if the first
      cout << "n=" << param::n << " |F_i|<=" << param::w << " d=";
      if (param::d>=param::n) cout << "n"; else cout << param::d;
      cout << " t=" << x->length << ": " << *x << endl;
    }
    if (!nxt.insert(x).second) { // Insert into the nxt set
      x->unref(); // It already existed in the set.
    }
    if (depth < param::w) { // If still allowed, recurse
      generate_next(compatible, next, robdd::Or(not_anti,robdd::Or(robdd::subset(c),robdd::supset(c))), depth+1);
    }
    compatible.push_back(c); // Track elements that can be chosen in a recursive call
  }
};

void tests() {
  if (param::n==4) {
    cout << enumerate(precomputed_subset[11]) << " = {013}" << endl;
    cout << enumerate(robdd::subset(precomputed_subset[5])) << " = {-,2,0,02}" << endl;
    cout << enumerate(robdd::supset(precomputed_subset[13])) << " = {023,0123}" << endl;
    const robdd::robdd * c = robdd::Or(precomputed_subset[13],precomputed_subset[10]);
    cout << enumerate(c) << " = {13,023}" << endl;
    cout << enumerate(subset(c)) << " = {-,3,2,23,1,13,0,03,02,023}" << endl;
    cout << enumerate(supset(c)) << " = {13,123,023,013,0123}" << endl;
  }
  if (param::n==5) {
    const robdd::robdd * prev = robdd::Or(precomputed_subset[14],precomputed_subset[21]);
    const robdd::robdd * next = robdd::Or(precomputed_subset[13],precomputed_subset[22]);
    cout << enumerate(prev) << " = {123,024}" << endl;
    cout << enumerate(next) << " = {023,124}" << endl;
    cout << enumerate(robdd::And(robdd::subset(prev), robdd::conj(robdd::subset(next)))) << " = {13,04}" << endl;
    cout << enumerate(robdd::canonicalize(prev)) << endl;
    cout << enumerate(robdd::canonicalize(next)) << endl;
    cout << enumerate(robdd::canonicalize(robdd::supset(prev))) << endl;
    cout << enumerate(robdd::canonicalize(robdd::supset(next))) << endl;
    cout << enumerate(robdd::canonicalize(robdd::subset(prev))) << endl;
    cout << enumerate(robdd::canonicalize(robdd::subset(next))) << endl;
    
    for (int k=0; k<2; k++) {
      const robdd::robdd * t = supset(k==0?prev:next);
      for (int i=0; i<param::n; i++) {
        const robdd::robdd * r = robdd::And(t, robdd::robdd(i,robdd::TRUE,robdd::FALSE).intern());
        //const robdd::robdd * r = robdd::remove_layer(t, i);
        auto r_sc = robdd::sat_count(r);
        cout << i << ": " << (r_sc.first << r_sc.second) << ", ";
        for (int j=0; j<param::n; j++) if (i!=j) {
          const robdd::robdd * s = robdd::And(r, robdd::robdd(j,robdd::TRUE,robdd::FALSE).intern());
          //const robdd::robdd * s = robdd::remove_layer(r, j);
          auto s_sc = robdd::sat_count(s);
          cout << " " << (s_sc.first << s_sc.second);
        }
        cout << ", " << robdd::get_element(r) << " " << robdd::get_non_element(r) << " " << enumerate(r) << endl;
      }
      /*for (int i=0; i<param::n; i++) {
        const robdd::robdd * r = robdd::And(t, robdd::robdd(i,robdd::TRUE,robdd::FALSE).intern());
        cout << i << ": " << enumerate(robdd::canonicalize(r)) << endl;
      }*/
    }
  }
}

int main(int argc, const char *argv[]) {
  for (int i=0; i<(1<<param::n); i++) {
    precomputed_subset[i] = construct(i);
  }
  cout << "Subsets precomputed." << endl;
//   tests();
  sequence* root = new sequence;
  for (int i=0; i<param::n; i++) {
    cur.insert(new sequence(root, precomputed_subset[(2<<i)-1]));
  }
  while (!cur.empty()) {
    cout << "Cache:" << cur.size() << "  robdd nodes:" << robdd::cache.size() << endl;
    for (sequence * s : cur) {
      seq = s;
      vector<const robdd::robdd *> compatible;
      for (int i : enumerate(robdd::conj(seq->forbidden)).result) {
        const robdd::robdd * r = precomputed_subset[i];
        assert(robdd::And(seq->forbidden, r) == robdd::FALSE);
        compatible.push_back(r);
      }
      generate_next(compatible, robdd::FALSE, robdd::FALSE, 1);
      seq->unref();
    }
    swap(cur,nxt);
    nxt.clear();
  }
    
  // make memchecker happy :)
  robdd::clear_cache();
  root->unref();
  return 0;
}