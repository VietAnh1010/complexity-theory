// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny loops i over the value range and tests digit distinctness
//     with nested pair loops, O((b - a) log**2 b); the Python's `str(i)`
//     and `set(r)` cost O(log b) per candidate, O((b - a) log b) in all.
//
//   how this label could be wrong, and what to check:
//     The label's n must be the value range b - a, but each candidate also
//     costs its digit count d = log b (`str(i)` and `set(r)`), so the
//     Python is O((b - a) log b). The Dafny compares every digit pair,
//     O(d**2) per candidate. Check the nested `p`/`q` loops against the
//     Python's `set(r)`.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 49, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 3,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1228_A. Distinct Digits  (problem 2892, solution 2892_914)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// r=[]
// flag=0
// for i in range(a,b+1):
//     tmp=i
//     r=[int(d) for d in str(i)]
//     s=set(r)
//     if(len(r)==len(s)):
//         flag=1
//         break
// if(flag):
//     print(tmp)
// else:
//     print("-1")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var flag := false;
  var tmp := 0;
  var i := a;
  while i <= b && !flag
    invariant a <= i
    decreases b - i + 1
  {
    tmp := i;
    var temp := i;
    var digits: seq<int> := [];
    if temp == 0 {
      digits := [0];
    } else {
      while temp > 0
        decreases temp
      {
        digits := digits + [temp % 10];
        temp := temp / 10;
      }
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
    if distinct { flag := true; }
    i := i + 1;
  }
  if flag {
    output := IntToString(tmp);
  } else {
    output := "-1";
  }
}
