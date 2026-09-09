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

// Label O(n) -- agrees. `SumSeq` recurses once per element, so it is charged
// |values|, and nothing else in the row depends on the input size.
method Solve(N: int, values: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= |values| + 6
{
  var ans := FloorDiv(N * (N + 1), 2);
  ans := ans - SumSeq(values);
  output := IntToString(ans) + "\n";
  steps := |values| + 6;
}
