// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-10
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Besides SortInts at O(n log n), the loop over n calls Gcd three
//     times per element, each costing Euclid's depth in the values, so the
//     true cost is O(n log n + n log max a_i); the Python math.gcd pays
//     the same value term.
//
//   how this label could be wrong, and what to check:
//     The label accounts for the sort but not for the Gcd calls, whose
//     Euclid depth depends on the values a_i. Check the loop body: Gcd(g,
//     lst[i]) is called twice and Gcd(l, running) once per element, each
//     O(log min) in the values; Python's math.gcd runs Euclid too, so the
//     label would only hold if values were bounded by a polynomial in n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 59, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString"], "loop_depth":
//     1, "loops": 1, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 1349_A. Orac and LCM  (problem 1871, solution 1871_156)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import gcd
//  
// n = int(input())
// lst = list(map(int, input().split()))
// 
// lst.sort()
//  
// g = gcd(lst[0],lst[1])
// l = int((lst[0]*lst[1])/(g))
//  
// for i in range(2,n):
//     l = gcd(l , int((lst[i]*g)/gcd(g,lst[i])))
//     g = gcd(g, lst[i])
//     
// print(l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma GcdNonneg(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures Gcd(a, b) >= 0
  decreases b
{
  if b == 0 {
  } else {
    GcdNonneg(b, a % b);
  }
}

lemma GcdPositive(a: int, b: int)
  requires a >= 0 && b >= 0
  requires a >= 1 || b >= 1
  ensures Gcd(a, b) >= 1
  decreases b
{
  if b == 0 {
  } else {
    GcdPositive(b, a % b);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| >= 2
  requires n <= |a_list|
  requires forall v :: v in a_list ==> v >= 1
{
  var lst := SortInts(a_list);
  SortIntsKeepsElems(a_list);
  assert {:split_here} forall v :: v in lst ==> v >= 1;
  assert lst[0] in lst && lst[1] in lst;
  assert lst[0] >= 1 && lst[1] >= 1;
  var g := Gcd(lst[0], lst[1]);
  GcdPositive(lst[0], lst[1]);
  assert {:split_here} g >= 1;
  var l := (lst[0] * lst[1]) / g;
  assert {:split_here} l >= 0;
  var i := 2;
  while i < n
    invariant 2 <= i
    invariant g >= 1
    invariant l >= 0
    decreases n - i
  {
    assert {:split_here} lst[i] in lst;
    assert lst[i] >= 1;
    var gi := Gcd(g, lst[i]);
    GcdPositive(g, lst[i]);
    assert {:split_here} gi >= 1;
    var running := (lst[i] * g) / gi;
    assert {:split_here} running >= 0;
    GcdNonneg(l, running);
    l := Gcd(l, running);
    g := Gcd(g, lst[i]);
    i := i + 1;
  }
  output := IntToString(l);
}
