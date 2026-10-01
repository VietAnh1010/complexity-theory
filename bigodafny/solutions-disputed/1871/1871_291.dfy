// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-10
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The single loop over |arr| makes three Gcd calls per element, each
//     O(log min(a, b)) in a value, giving O(n log max a_i); the Python's
//     own gcd loop pays the same Euclid steps.
//
//   how this label could be wrong, and what to check:
//     The label counts only the n elements, but each iteration calls Gcd
//     whose cost is Euclid's depth in the values. Check Gcd(current,
//     arr[i]) and Gcd(lcm, running) in the loop and the hand-written
//     while-b gcd in the Python; if the values were constants the label
//     would stand, but a_i is only capped by the statement.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 56, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString"], "loop_depth":
//     1, "loops": 1, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1349_A. Orac and LCM  (problem 1871, solution 1871_291)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def gcd(a, b):
//     while b:
//         a, b = b, a % b
//     return a
// 
// def solve(array):
//     lcm = (array[0] * array[1])//gcd(array[0], array[1])
//     current = lcm
//     for i in range(2, len(array)):
//         running = (current * array[i])//gcd(current, array[i])
//         lcm = gcd(lcm, running)
//         current = gcd(current, array[i])
//     print(lcm)
//     return
// 
// n = int(input())
// arr = list(map(int, input().split(' ')))
// solve(arr)
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
  requires forall v :: v in a_list ==> v >= 1
{
  var arr := a_list;
  assert arr[0] in arr && arr[1] in arr;
  assert {:split_here} arr[0] >= 1 && arr[1] >= 1;
  GcdPositive(arr[0], arr[1]);
  var lcm := (arr[0] * arr[1]) / Gcd(arr[0], arr[1]);
  assert {:split_here} lcm >= 0;
  var current := lcm;
  var i := 2;
  while i < |arr|
    invariant 2 <= i
    invariant current >= 0
    invariant lcm >= 0
    decreases |arr| - i
  {
    assert {:split_here} arr[i] in arr;
    assert arr[i] >= 1;
    GcdPositive(current, arr[i]);
    var gi := Gcd(current, arr[i]);
    assert {:split_here} gi >= 1;
    var running := (current * arr[i]) / gi;
    assert {:split_here} running >= 0;
    GcdNonneg(lcm, running);
    lcm := Gcd(lcm, running);
    GcdNonneg(current, arr[i]);
    current := Gcd(current, arr[i]);
    i := i + 1;
  }
  output := IntToString(lcm);
}
