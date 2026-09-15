// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r2-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The problem statement caps n at 4 (`1 <= n <= 4`, the surviving
//     corners of a rectangle), so the nested loop `while i<n {... while
//     j<n ...}` in Solve executes at most 4*3/2=6 total inner-body
//     evaluations for any valid input rather than a quantity that grows
//     with n; the Python's identical double loop over s is bounded the
//     same way.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) implies the double loop's cost grows without bound
//     as n increases. Reread the problem statement's Input section and
//     confirm n really is capped at 4 (the vertex count of a rectangle)
//     rather than being a general array-size n; if the cap is genuine and
//     fixed across all valid inputs, both loops run a bounded number of
//     times and the true class is O(1), not O(n**2). If some other reading
//     of the statement lets n scale further, the label stands.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 54, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt",
//     "ParseIntFrom"], "loop_depth": 2, "loops": 3, "recursive_helpers":
//     2, "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_54)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin
// n=int(stdin.readline().strip())
// s=[]
// for i in range(n):
//     
//     a,b=map(int,stdin.readline().strip().split())
//     s.append([a,b])
// ans=-1
// for i in range(n):
//     for j in range(i+1,n):
//         if( s[i][0]!=s[j][0] and  s[i][1]!=s[j][1] ):
//             
//             ans=abs(s[i][0]-s[j][0] )*  abs(s[i][1]-s[j][1] )  
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}


method Solve(n: int, values: seq<seq<string>>) returns (output: string)
  requires n >= 0
  requires |values| == n
  requires forall k :: 0 <= k < n ==> |values[k]| >= 2
{
  var xs: seq<int> := [];
  var ys: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |xs| == i
    invariant |ys| == i
    decreases n - i
  {
    xs := xs + [ParseInt(values[i][0])];
    ys := ys + [ParseInt(values[i][1])];
    i := i + 1;
  }
  var ans := -1;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |xs| == n
    invariant |ys| == n
    decreases n - i
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      decreases n - j
    {
      if xs[i] != xs[j] && ys[i] != ys[j] {
        ans := AbsInt(xs[i] - xs[j]) * AbsInt(ys[i] - ys[j]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
