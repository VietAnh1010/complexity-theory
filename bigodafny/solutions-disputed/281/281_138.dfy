// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     After `SortInts(a_list)` the loop calls the row's recursive `Gcd(g,
//     xs[i])` for each element, charged Euclid's depth, so the cost is O(n
//     log n + n log max a_i); the Python's hand-written gcd loop pays the
//     same value term.
//
//   how this label could be wrong, and what to check:
//     The label counts the sort but not the Euclid steps. Check the loop
//     calling `Gcd(g, xs[i])` n times: each call costs Euclid's depth in
//     the values, a value term the label's n does not name. The Python's
//     own `gcd` while-loop pays the same.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 29, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString"], "loop_depth":
//     1, "loops": 1, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 389_A. Fox and Number Game  (problem 281, solution 281_138)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// x = list(sorted(map(int, input().split())))
// 
// 
// def gcd(a, b):
//     while b > 0:
//         a, b = b, a % b
//     return a
// 
// tgcd = x.pop(0)
// for i in x:
//     tgcd = gcd(tgcd, i)
// 
// print(tgcd * n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| >= 1
  requires forall x :: x in a_list ==> x >= 0
{
  var xs := SortInts(a_list);
  SortIntsKeepsElems(a_list);
  assert xs[0] in xs;
  var g := xs[0];
  var i := 1;
  while i < |xs|
    invariant 1 <= i
    invariant g >= 0
    decreases |xs| - i
  {
    assert xs[i] in xs;
    g := Gcd(g, xs[i]);
    i := i + 1;
  }
  output := IntToString(g * n);
}

function Gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures Gcd(a, b) >= 0
  decreases b
{
  if b == 0 then a else Gcd(b, a % b)
}
