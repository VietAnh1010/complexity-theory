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
  output := ""; // TODO: translate the Python above
}
