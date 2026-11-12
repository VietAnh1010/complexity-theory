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

ghost function PP(w: bool, n: nat, i: nat): nat
{
  if w then n + 1 + i else i
}

ghost opaque function Pot(j: nat, m: nat, p: nat): nat
{
  j * m + p
}

lemma PotStep(j: nat, m: nat, p: nat, p2: nat)
  requires p <= p2
  ensures Pot(j, m, p) <= Pot(j, m, p2)
  ensures p < p2 ==> Pot(j, m, p) < Pot(j, m, p2)
{
  reveal Pot();
}

lemma PotJump(j: nat, m: nat, p: nat, p2: nat)
  requires p < m
  ensures Pot(j, m, p) < Pot(j + 1, m, p2)
{
  reveal Pot();
  CostMulDistrib(j, 1, j + 1, m);
}

lemma PotBound(j: nat, T: nat, m: nat, p: nat)
  requires j <= T && p < m
  ensures Pot(j, m, p) < (T + 1) * m
{
  reveal Pot();
  CostMulMonoLeft(j, T, m);
  CostMulDistrib(T, 1, T + 1, m);
}

method Solve(v0: string, v1: string) returns (output: string)
  requires |v0| >= 1
{
  var s := v0;
  var t := v1;
  var i := 0;
  var j := 0;
  var nt := 0;
  var ar := 0;
  var at := 0;
  var done := false;
  ghost var w := false;
  while i <= |s| && j < |t| && !done
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |t|
    invariant |s| == |v0|
    invariant w ==> (j < |t| ==> forall q :: 0 <= q < i ==> s[q] != t[j])
    decreases if done then 0 else 1, (|t| + 1) * (2 * |s| + 2) - Pot(j, 2 * |s| + 2, PP(w, |s|, i))
  {
    ghost var jOld := j;
    ghost var pOld := PP(w, |s|, i);
    ghost var stuck := i == |s| && w;
    assert stuck ==> forall q :: 0 <= q < |s| ==> s[q] != t[j];
    PotBound(j, |t|, 2 * |s| + 2, PP(w, |s|, i));
    if i == |s| {
      i := 0;
      ar := 1;
      w := true;
    }
    var found := false;
    var idx := 0;
    while idx < |s|
      invariant 0 <= idx <= |s|
      invariant found <==> exists q :: 0 <= q < idx && s[q] == t[j]
      decreases |s| - idx
    {
      if s[idx] == t[j] {
        found := true;
      }
      idx := idx + 1;
    }
    assert stuck ==> !found;
    if found {
      if s[i] == t[j] {
        s := s[i := ':'];
        j := j + 1;
        i := i + 1;
        w := false;
      } else {
        i := i + 1;
        at := 1;
      }
    } else {
      nt := 1;
      done := true;
    }
    if done {
    } else if j == jOld {
      PotStep(j, 2 * |s| + 2, pOld, PP(w, |s|, i));
    } else {
      PotJump(jOld, 2 * |s| + 2, pOld, PP(w, |s|, i));
    }
    if !done {
      PotBound(j, |t|, 2 * |s| + 2, PP(w, |s|, i));
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
