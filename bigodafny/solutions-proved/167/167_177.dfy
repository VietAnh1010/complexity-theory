// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny computes `x := ISqrt(n)` and loops `while i < x`, at most
//     sqrt(n) iterations of O(1) work, so the cost is O(sqrt n); the
//     Python's `range(1, x)` has the same bound.
//
//   how this label could be wrong, and what to check:
//     The label is linear in the input value n, but the loop runs i from 1
//     to floor(sqrt(n)), about sqrt(n) iterations. Check the loop bound `x
//     = math.floor(math.sqrt(n))` (`ISqrt(n)` in the Dafny); the class is
//     O(sqrt n), outside the vocabulary.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1184_A1. Heidi Learns Hashing (Easy)  (problem 167, solution 167_177)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = int(input())
// x = math.floor(math.sqrt(n))
// p = 0
// for i in range(1, x):
// 	if (n-1-i**2-i)%(2*i) == 0 :
// 		print(i,  (n-1-i**2-i)//(2*i))
// 		p = 1
// 		break
// if not p:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 10 * ISqrt(n) + CeilLog2(n) + 10 + 2 * |output|
{
  steps := 1 + ISqrtSteps(n);
  ISqrtStepsBound(n);
  var x := ISqrt(n);
  var p := 0;
  var result := "";
  var i := 1;
  while i < x && p == 0
    invariant 1 <= i && i - 1 <= x
    invariant p == 0 ==> result == ""
    invariant steps <= 1 + ISqrtSteps(n) + 10 * (i - 1) + 2 * |result|
    decreases x - i
  {
    var expr := n - 1 - i * i - i;
    steps := steps + 10;
    if expr % (2 * i) == 0 {
      result := IntToString(i) + " " + IntToString(expr / (2 * i));
      IntToStringDigits(i);
      IntToStringDigits(expr / (2 * i));
      steps := steps + Digits(i) + 1 + 2 * Digits(expr / (2 * i));
      p := 1;
    }
    i := i + 1;
  }
  if p == 0 {
    result := "NO";
    steps := steps + 1;
  }
  output := result;
}
