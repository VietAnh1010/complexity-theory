// 463_B. Caisa and Pylons  (problem 2015, solution 2015_175)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// h = [int(x) for x in input().split()]
//
// ans = 0
// for i in h:
//     ans = max(ans,i)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |a_list| + 3
{
  steps := 1;
  var h := ParseInts(a_list);
  // ParseInts: one constant-cost ParseInt call per token.
  steps := steps + |a_list| + 1;
  var ans := 0;
  var i := 0;
  ghost var ibase := steps;
  while i < |h|
    invariant 0 <= i <= |h|
    invariant steps <= ibase + 3 * i
    decreases |h| - i
  {
    if h[i] > ans { ans := h[i]; steps := steps + 1; }
    i := i + 1;
    steps := steps + 2;
  }
  output := IntToString(ans);
  steps := steps + 1;
}
