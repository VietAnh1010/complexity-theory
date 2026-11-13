// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny loops i from a to b, extracting digits and comparing all
//     pairs in nested `p`/`q` loops, O((b - a) log**2 b); the Python
//     extracts digits and builds `set(l)`, O((y - x) log y), so neither is
//     O(n**2).
//
//   how this label could be wrong, and what to check:
//     The loop runs over the VALUE range x..y until a number with distinct
//     digits appears, each candidate costing its digit count d = log y, so
//     the Python is O((y - x) log y), not a square. The Dafny checks
//     distinctness by comparing every digit pair, O(d**2) per candidate,
//     where the Python uses `set(l)`. Check the Dafny's nested `p`/`q`
//     loops.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 47, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 3,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1228_A. Distinct Digits  (problem 2892, solution 2892_1216)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x,y=map(int,input().split())
// for i in range(x,y+1,1):
//   l=[]
//   temp=i
//   while temp>0:
//       r=temp%10
//       l.append(r)
//       temp=temp//10
//   s=set(l) 
//   a=len(s)
//   b=len(l)
//   if a==b:
//       print(i)
//       break
// if a!=b:
//      print('-1')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var found := false;
  var ans := 0;
  var i := a;
  while i <= b && !found
    invariant a <= i
    decreases b - i + 1
  {
    var temp := i;
    var digits: seq<int> := [];
    while temp > 0
      decreases temp
    {
      digits := digits + [temp % 10];
      temp := temp / 10;
    }
    var distinct := true;
    var p := 0;
    while p < |digits|
      invariant 0 <= p <= |digits|
      decreases |digits| - p
    {
      var q := p + 1;
      while q < |digits|
        invariant p < q <= |digits|
        decreases |digits| - q
      {
        if digits[p] == digits[q] { distinct := false; }
        q := q + 1;
      }
      p := p + 1;
    }
    if distinct {
      found := true;
      ans := i;
    }
    i := i + 1;
  }
  if found {
    output := IntToString(ans);
  } else {
    output := "-1";
  }
}
