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

method Solve(n: int, k: int, s: string) returns (output: string)
{
  var ans := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
  {
    var cnt := 0;
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
    {
      if s[j] == s[i] { cnt := cnt + 1; }
      j := j + 1;
    }
    if cnt > ans { ans := cnt; }
    i := i + 1;
  }
  output := if ans <= k then "YES" else "NO";
}
