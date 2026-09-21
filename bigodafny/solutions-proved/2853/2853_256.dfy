// 841_A. Generous Kefa  (problem 2853, solution 2853_256)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def list_input():
//     return list(map(int,input().split()))
// def map_input():
//     return map(int,input().split())
// def map_string():
//     return input().split()
//
// n,k = map_input()
// s = input()
// ans = 0
// for i in s:
//     ans = max(ans,s.count(i))
// if ans <= k:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulMonoRight2853(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

method Solve(n: int, k: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= (2 * |s| + 4) * |s| + 3
{
  steps := 1;
  var ans := 0;
  var i := 0;
  ghost var base1 := steps;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant steps <= base1 + (2 * |s| + 4) * i
    decreases |s| - i
  {
    var cnt := 0;
    var j := 0;
    ghost var base2 := steps;
    while j < |s|
      invariant 0 <= j <= |s|
      invariant steps <= base2 + 2 * j
      decreases |s| - j
    {
      if s[j] == s[i] { cnt := cnt + 1; }
      j := j + 1;
      steps := steps + 2;
    }
    if cnt > ans { ans := cnt; }
    i := i + 1;
    steps := steps + 4;
  }
  MulMonoRight2853(2 * |s| + 4, i, |s|);
  output := if ans <= k then "YES" else "NO";
  steps := steps + 1;
}
