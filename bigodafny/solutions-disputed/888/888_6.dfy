// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3-fix
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     ReverseSeq peels s[1..] with + [s[0]], which is O(|s|) by the
//     recursion row, the Ans build is one pass, and in the main loop p and
//     q never decrease (p advances in the inner while, q once per outer
//     pass), giving O(n) total. The Python does the same single D[::-1]
//     and two-pointer sweep, so it is linear and the O(n**2) label is
//     wrong.
//
//   how this label could be wrong, and what to check:
//     The label claims quadratic, but this is a two-pointer sweep where p
//     and q only ever increase. Find the outer while with decreases twoN -
//     q and the inner while advancing p; confirm each outer pass
//     increments q (or exits) and the inner loop never resets p, then
//     compare the Python's identical p and q updates.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 65, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1358_D. The Best Vacation  (problem 888, solution 888_6)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x=map(int,input().split());D=list(map(int,input().split()));Ans=[];D+=D;D=D[::-1];d=0;p=0;q=0;tot=0;ans=0
// for i in D:Ans.append(i*(i+1)//2)
// while p<2*n and q<2*n:
//     while p<2*n and q<2*n and d+D[p]<x:d+=D[p];tot+=Ans[p];p+=1
//     if p==q:k=D[p]-x+d;tot+=Ans[p]-k*(k+1)//2;ans=max(ans,tot);d=0;tot=0;p+=1;q+=1    
//     elif p<2*n and q<2*n:k=D[p]-x+d;tot+=Ans[p]-k*(k+1)//2;ans=max(ans,tot);d-=min(D[q],d);tot-=Ans[q];tot-=Ans[p]-k*(k+1)//2;q+=1
// print(ans)          
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 0
{
  var doubled := a_list + a_list;
  var D := ReverseSeq(doubled);
  var twoN := 2 * n;
  var Ans: seq<int> := [];
  var t := 0;
  while t < |D|
    invariant 0 <= t <= |D|
    invariant |Ans| == t
    decreases |D| - t
  {
    var v := D[t];
    Ans := Ans + [v * (v + 1) / 2];
    t := t + 1;
  }
  var d := 0;
  var p := 0;
  var q := 0;
  var tot := 0;
  var ans := 0;
  // q advances on every iteration that takes a branch; the only iteration that
  // does not is the one where the inner loop drove p to twoN, and that one is
  // the last. Hence the lexicographic measure.
  while p < twoN && q < twoN
    invariant 0 <= p <= twoN && 0 <= q <= twoN
    invariant |D| == twoN && |Ans| == twoN
    decreases twoN - q, twoN - p
  {
    while p < twoN && q < twoN && d + D[p] < m
      invariant 0 <= p <= twoN
      decreases twoN - p
    {
      d := d + D[p];
      tot := tot + Ans[p];
      p := p + 1;
    }
    if p == q {
      var k := D[p] - m + d;
      tot := tot + Ans[p] - k * (k + 1) / 2;
      if tot > ans { ans := tot; }
      d := 0;
      tot := 0;
      p := p + 1;
      q := q + 1;
    } else if p < twoN && q < twoN {
      var k := D[p] - m + d;
      tot := tot + Ans[p] - k * (k + 1) / 2;
      if tot > ans { ans := tot; }
      var minv := if D[q] < d then D[q] else d;
      d := d - minv;
      tot := tot - Ans[q];
      tot := tot - (Ans[p] - k * (k + 1) / 2);
      q := q + 1;
    }
  }
  output := IntToString(ans) + "\n";
}

function ReverseSeq(s: seq<int>): seq<int>
  ensures |ReverseSeq(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseSeq(s[1..]) + [s[0]]
}
