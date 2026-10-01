// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The gcd loop over arr calls Gcd n times, each charged O(log min(a,
//     b)), so the cost is O(n log max a_i) plus the linear MaxSeq. The
//     Python's math.gcd loop pays the same Euclid depth, so the label is
//     wrong for both programs.
//
//   how this label could be wrong, and what to check:
//     The label counts only the list scan. The loop calls Gcd(g, arr[i]) n
//     times and the model charges Euclid's depth O(log min(a,b)) per call,
//     a value term in a_i <= 10^9 that n does not account for. Check the
//     constraint a_i <= 10^9 in the statement; if the gcd chain is treated
//     as amortised O(n + log max) the O(n) label would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 34, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "MaxSeq"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 346_A. Alice and Bob  (problem 1386, solution 1386_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
//
// n = int(input())
// arr = list(map(int, input().split()))
//
// gcd = 0
// for num in arr:
// 	gcd = math.gcd(gcd, num)
//
// moves = max(arr) / gcd - n
// if moves % 2:
// 	print('Alice')
// else:
// 	print('Bob')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma GcdPos(x: int, y: int)
  requires x >= 0 && y >= 0 && (x > 0 || y > 0)
  ensures Gcd(x, y) > 0
  decreases y
{
  if y == 0 {
  } else {
    GcdPos(y, x % y);
  }
}

method Solve(a: int, b_list: seq<int>) returns (output: string)
  requires 1 <= a <= |b_list|
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
{
  var n := a;
  var arr := b_list;
  var g := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant g >= 0
    invariant i > 0 ==> g > 0
    decreases n - i
  {
    GcdPos(g, arr[i]);
    g := Gcd(g, arr[i]);
    i := i + 1;
  }
  var mx := MaxSeq(arr);
  var moves := FloorDiv(mx, g) - n;
  output := if FloorMod(moves, 2) != 0 then "Alice" else "Bob";
}
