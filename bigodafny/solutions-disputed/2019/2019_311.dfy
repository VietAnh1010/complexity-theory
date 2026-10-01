// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     ParseInts(c_list) converts the n tokens once and the single loop
//     `while i < n && !stopped` does O(1) arithmetic per day, so Solve is
//     O(n). The Python's list(map(int, input().split())) and one for loop
//     are linear as well, so O(n**2) matches neither. Each token is a
//     number of at most three digits (a_i <= 100), which I treated as a
//     constant-width parse, not a second size.
//
//   how this label could be wrong, and what to check:
//     The label claims quadratic work, but there is one loop. Check `while
//     i < n && !stopped`: it does O(1) work per day and the other cost is
//     ParseInts(c_list) once; if the tokens are one short number each,
//     parsing is linear in the count too.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 44, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInts"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 839_A. Arya and Bran  (problem 2019, solution 2019_311)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// a = list(map(int, input().split()))
// count = tank = 0
// for i in range(n):
// 	tank+=a[i]
// 	if tank>=8:
// 		count+=1
// 		tank-=8
// 		k-=8
// 	else:
// 		count+=1
// 		k-=tank
// 		tank=0
// 	if k<=0:
// 		break
// if k>0:
// 	print(-1)
// else:
// 	print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<string>) returns (output: string)
  requires a >= 0 && b >= 0
  // Either the array is long enough outright, or every entry is positive -- in
  // which case k falls by at least 1 per step, so the loop stops within b
  // steps and never reaches past the end. Both violating stored inputs take
  // the second branch, and the row's Python survives them for this reason.
  requires a <= |c_list|
       || (1 <= b <= |c_list| && forall t :: 0 <= t < |c_list| ==> ParseInts(c_list)[t] >= 1)
{
  var n := a;
  var k := b;
  var arr := ParseInts(c_list);
  var count := 0;
  var tank := 0;
  var i := 0;
  var stopped := false;
  while i < n && !stopped
    invariant 0 <= i
    invariant |arr| == |c_list|
    invariant tank >= 0
    invariant a <= |c_list| ==> i <= a
    invariant (forall t :: 0 <= t < |arr| ==> arr[t] >= 1) ==> k <= b - i
    invariant !stopped ==> (k > 0 || i == 0)
    decreases n - i
  {
    tank := tank + arr[i];
    if tank >= 8 {
      count := count + 1;
      tank := tank - 8;
      k := k - 8;
    } else {
      count := count + 1;
      k := k - tank;
      tank := 0;
    }
    if k <= 0 {
      stopped := true;
    }
    i := i + 1;
  }
  if k > 0 {
    output := IntToString(-1);
  } else {
    output := IntToString(count);
  }
}
