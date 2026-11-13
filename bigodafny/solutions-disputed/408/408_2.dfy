// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both the Python and the Dafny read only `a[i][0]` and `a[i][1]`
//     (`pairs_list[i][0]`, `pairs_list[i][1]`) of each of n rows, so the
//     cost is O(n); a round is a fixed pair, never walked.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each row is one round's two dice
//     values and both programs read only `[0]` and `[1]`. Check the input
//     format: if every line holds exactly two numbers, m is constant and
//     the class is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 703_A. Mishka and Game  (problem 408, solution 408_2)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// m=0
// c=0
// a=[]
// for i in range(n):
// 	a.append(list(map(int,input().split())))	
// 	if a[i][0]>a[i][1]:
// 		m+=1
// 	if a[i][1]>a[i][0]:
// 		c+=1
// if m>c:
// 	print("Mishka")
// if m<c:
// 	print("Chris")			
// if m==c:
// 	print("Friendship is magic!^^")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, pairs_list: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |pairs_list| ==> |pairs_list[k]| >= 2
{
  var m := 0;
  var c := 0;
  var i := 0;
  while i < |pairs_list|
    invariant 0 <= i
    decreases |pairs_list| - i
  {
    var a := pairs_list[i][0];
    var b := pairs_list[i][1];
    if a > b { m := m + 1; }
    if b > a { c := c + 1; }
    i := i + 1;
  }
  if m > c {
    output := "Mishka";
  } else if m < c {
    output := "Chris";
  } else {
    output := "Friendship is magic!^^";
  }
}
