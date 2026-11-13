// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The single loop over `a_list` calls the recursive `Gcd(q,
//     a_list[i])` per element, each charged O(log min) in the values,
//     giving O(n log max a_i); the Python's `math.gcd` loop pays the same
//     Euclid depth.
//
//   how this label could be wrong, and what to check:
//     The label counts the n gcd calls as unit steps. Check the loop
//     calling `Gcd(q, a_list[i])`: each call costs Euclid's depth in the
//     values, a value term. The Python's `math.gcd` runs Euclid too, so
//     the label, not the translation, omits it.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString"], "loop_depth":
//     1, "loops": 1, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 389_A. Fox and Number Game  (problem 281, solution 281_250)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #CF389A
// n,q=int(input()),0
// import math 
// for i in map(int,input().split()):q=math.gcd(q,i)
// print(q*n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires forall x :: x in a_list ==> x >= 0
{
  var q := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i
    invariant q >= 0
    decreases |a_list| - i
  {
    assert a_list[i] in a_list;
    q := Gcd(q, a_list[i]);
    i := i + 1;
  }
  output := IntToString(q * n);
}

function Gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures Gcd(a, b) >= 0
  decreases b
{
  if b == 0 then a else Gcd(b, a % b)
}
