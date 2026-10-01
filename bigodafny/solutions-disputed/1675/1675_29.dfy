// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each outer iteration scans all of s in `while idx < |s|`, and the
//     outer loop advances i and wraps to 0 once per consumed character of
//     t (e.g. s = a^k b^k with t alternating b and a), giving up to
//     |s|*|t| iterations of O(|s|) work, a cubic bound O(|s|^2 |t|)
//     outside the vocabulary. The Python `t[j] in s` scans s per iteration
//     the same way, so the label is wrong; the cubic worst case is my
//     derivation, not a stated bound.
//
//   how this label could be wrong, and what to check:
//     The label stops at quadratic, but there is a full scan of s inside a
//     loop that can itself run about |s|*|t| times. Check the inner `while
//     idx < |s|` scan (no early exit) inside the `while i <= |s| && j <
//     |t|` loop, and whether i wraps once per consumed character of t.
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
