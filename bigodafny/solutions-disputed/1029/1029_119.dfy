// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : other
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3-05
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     BitOr is a hand-written recursion that halves both arguments,
//     costing O(log max a_i) per call, so the Dafny is O(n log max a + m
//     log max b); Python's | on ints of at most 10^9 is O(1), so the
//     translation reimplemented a primitive and the Python really is
//     O(n+m).
//
//   how this label could be wrong, and what to check:
//     The label O(n+m) assumes each element costs O(1). Find BitOr in the
//     Dafny: it recurses with a/2 and b/2 until one argument is 0, so each
//     call costs the bit length of the values. Then check the Python line
//     f1|=int(x), a machine-word OR that is O(1) for values up to 10^9; if
//     so the Python is O(n+m) and only the Dafny pays the value term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 37, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 631_A. Interview  (problem 1029, solution 1029_119)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// f1=f2=0
// for x in input().split(): f1|=int(x)
// for x in input().split(): f2|=int(x)
// print(f1+f2)
//   
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function BitOr(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures BitOr(a, b) >= 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else 2 * BitOr(a / 2, b / 2) + (if a % 2 == 1 || b % 2 == 1 then 1 else 0)
}


method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
  requires forall k :: 0 <= k < |a_list| ==> a_list[k] >= 0
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 0
{
  var f1 := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant f1 >= 0
    decreases |a_list| - i
  {
    f1 := BitOr(f1, a_list[i]);
    i := i + 1;
  }
  var f2 := 0;
  i := 0;
  while i < |b_list|
    invariant 0 <= i <= |b_list|
    invariant f2 >= 0
    decreases |b_list| - i
  {
    f2 := BitOr(f2, b_list[i]);
    i := i + 1;
  }
  output := IntToString(f1 + f2);
}
