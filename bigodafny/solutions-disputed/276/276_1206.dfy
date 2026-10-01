// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the test triples and calls MaxSeq, MinSeq, CountEq
//     and IndexOfEq on a length-3 seq, constant work per test, then Join
//     over n parts, so cost is O(n); the Python's count/max/min over a
//     3-list is also constant.
//
//   how this label could be wrong, and what to check:
//     The label assumes variable row width m. Check the statement: each
//     test line holds exactly three integers x,y,z and the Dafny requires
//     |r| == 3; MaxSeq, MinSeq, CountEq and IndexOfEq run over a
//     three-element seq.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 49, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "MaxSeq",
//     "MinSeq"], "loop_depth": 1, "loops": 1, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1385_A. Three Pairwise Maximums  (problem 276, solution 276_1206)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     ls=[int(a) for a in input().split()]
//     ls1=[1]*3
//         
//     if ls.count(max(ls))>1:
//         if ls.count(max(ls))==3:
//             ls1=ls
//         else:
//             ls1[ls.index(min(ls))]=min(ls)
//             ls1[ls.index(min(ls))-1]=max(ls)
//         
//         print("YES")
//         for _ in range(3):
//             print(ls1[_], end=' ' )
//         print('\n')
//     else:
//         print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, abc_list: seq<seq<int>>) returns (output: string)
  requires forall r :: r in abc_list ==> |r| == 3
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |abc_list|
    invariant 0 <= i
    decreases n - i
  {
    var ls := abc_list[i];
    var mx := MaxSeq(ls);
    var mn := MinSeq(ls);
    var cmax := CountEq(ls, mx);
    if cmax > 1 {
      var ls1: seq<int>;
      if cmax == 3 {
        ls1 := ls;
      } else {
        var imin := IndexOfEq(ls, mn);
        var idx2 := if imin == 0 then 2 else imin - 1;
        ls1 := [1, 1, 1];
        if imin < |ls1| { ls1 := ls1[imin := mn]; }
        if idx2 < |ls1| { ls1 := ls1[idx2 := mx]; }
      }
      var line := IntToString(ls1[0]) + " " + IntToString(ls1[1]) + " " + IntToString(ls1[2]) + " ";
      parts := parts + ["YES\n" + line + "\n\n"];
    } else {
      parts := parts + ["NO\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}

function CountEq(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + CountEq(s[1..], v)
}

function IndexOfEq(s: seq<int>, v: int): int
  ensures 0 <= IndexOfEq(s, v)
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == v then 0
  else 1 + IndexOfEq(s[1..], v)
}
