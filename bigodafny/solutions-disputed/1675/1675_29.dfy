// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-09
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer while does up to |t| passes over s of |s|+1 steps each (i
//     wraps to 0 when i==|s|), and every step runs the inner idx scan over
//     |s| (Python's `t[j] in s` list scan does the same), so the worst
//     case is O(|s|*|t|*|s|), cubic rather than O(n**2).
//
//   how this label could be wrong, and what to check:
//     The label assumes quadratic cost, but the outer loop wraps over s
//     repeatedly (once per matched letter of t) and each outer step also
//     rescans s for t[j]. Open the Dafny's outer while and inner idx loop,
//     and the Python's `t[j] in s`, and construct s with distinct letters
//     and t its reverse to confirm about n passes of n steps of n scan.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 66, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": [], "loop_depth": 2, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 448_B. Suffix Structures  (problem 1675, solution 1675_29)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// t=input()
// x=set(s)
// s=list(s)
// i=0
// j=0	
// nt=0
// ar=0
// at=0
// while i<=len(s) and j<len(t):
// 	if i==len(s):
// 			i=0
// 			ar=1
// 	if t[j] in s:
// 		if s[i]==t[j]:
// 			s[i]=':'
// 			j+=1
// 			i+=1
// 		else:
// 			i+=1
// 			at=1
// 	else:
// 		nt=1
// 		break
// if nt==0 and len(s)==len(t):
// 	at=0
// else:
// 	at=1
// if nt==1:
// 	print('need tree')
// elif at==ar==1:
// 	print('both')
// elif at==1:
// 	print('automaton')
// elif ar==1:
// 	print('array')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v0: string, v1: string) returns (output: string)
  requires |v0| >= 1
  // i sweeps s and wraps; it terminates because t[j] is known to occur in s,
  // but the measure is the distance to that occurrence, not a loop bound.
  decreases *
{
  var s := v0;
  var t := v1;
  var i := 0;
  var j := 0;
  var nt := 0;
  var ar := 0;
  var at := 0;
  var done := false;
  while i <= |s| && j < |t| && !done
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |t|
    invariant |s| == |v0|
    decreases *
  {
    if i == |s| {
      i := 0;
      ar := 1;
    }
    var found := false;
    var idx := 0;
    while idx < |s|
      invariant 0 <= idx <= |s|
      decreases |s| - idx
    {
      if s[idx] == t[j] {
        found := true;
      }
      idx := idx + 1;
    }
    if found {
      if s[i] == t[j] {
        s := s[i := ':'];
        j := j + 1;
        i := i + 1;
      } else {
        i := i + 1;
        at := 1;
      }
    } else {
      nt := 1;
      done := true;
    }
  }
  if nt == 0 && |s| == |t| {
    at := 0;
  } else {
    at := 1;
  }
  if nt == 1 {
    output := "need tree";
  } else if at == 1 && ar == 1 {
    output := "both";
  } else if at == 1 {
    output := "automaton";
  } else if ar == 1 {
    output := "array";
  } else {
    output := "";
  }
}
