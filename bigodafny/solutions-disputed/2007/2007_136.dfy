// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop `|ans| < n` does constant work per step (two reads of
//     edges[i-1]), and the parts/Join loop is linear, so the Dafny is
//     O(n); the Python's inner `for c in l[i-1]` and `b in l[a-1]` scan
//     2-element lists, so no m dimension exists there either.
//
//   how this label could be wrong, and what to check:
//     The label O(n*m) assumes rows have a variable width m, but each row
//     of `edges` is exactly 2 integers (the Dafny requires |edges[k]| == 2
//     and the problem gives a_{i,1}, a_{i,2}). Check the statement's input
//     format and the Python's `for c in l[i-1]`, which iterates a
//     2-element list.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 44, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString", "Join"], "loop_depth":
//     1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1095_D. Circular Dance  (problem 2007, solution 2007_136)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=[]
// a,b=0,0
// for i in range(n):
//     s=list(map(int,input().split(" ")))
//     a=int(s[0])
//     b=int(s[1])
//     l.append([a,b])
// ans=[1]
// a,b=l[0][0],l[0][1]
// if b in l[a-1]:
//     ans.append(a)
//     ans.append(b)
//     i=a
//     j=b
// else:
//     ans.append(b)
//     ans.append(a)
//     i=b
//     j=a
// while len(ans)<n:
//     for c in l[i-1]:
//         if c!=j:
//             ans.append(c)
//             break
//     i=j
//     j=c
// q=''
// q+=str(ans[0])
// for i in range(1,n):
//     q+=' '+str(ans[i])
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
  requires n == |edges|
  requires n >= 1
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| == 2
  requires forall k :: 0 <= k < |edges| ==> 1 <= edges[k][0] <= n
  requires forall k :: 0 <= k < |edges| ==> 1 <= edges[k][1] <= n
  decreases *
{
  var ans: seq<int> := [1];
  var a := edges[0][0];
  var b := edges[0][1];
  var i: int;
  var j: int;
  if edges[a-1][0] == b || edges[a-1][1] == b {
    ans := ans + [a, b];
    i := a;
    j := b;
  } else {
    ans := ans + [b, a];
    i := b;
    j := a;
  }
  while |ans| < n
    invariant 1 <= i <= n
    invariant 1 <= j <= n
    decreases *
  {
    var c := if edges[i-1][0] != j then edges[i-1][0] else edges[i-1][1];
    ans := ans + [c];
    i := j;
    j := c;
  }
  var parts: seq<string> := [];
  var idx := 0;
  while idx < |ans|
    decreases |ans| - idx
  {
    parts := parts + [IntToString(ans[idx])];
    idx := idx + 1;
  }
  output := Join(parts, " ");
}
