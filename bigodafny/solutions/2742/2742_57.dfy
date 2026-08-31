// 440_A. Forgotten Episode  (problem 2742, solution 2742_57)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// ans=n*(n+1)//2
// for elem in a:
//     ans-=elem
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
