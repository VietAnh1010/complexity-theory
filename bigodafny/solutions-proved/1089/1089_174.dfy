// 124_A. The number of positions  (problem 1089, solution 1089_174)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # Believe you can and you're halfway there. Theodore Roosevelt
// # by : Blue Edge - Create some chaos
// 
// n,a,b=map(int,input().split())
// print(min(n-a,b+1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(1) -- agrees. Straight-line arithmetic on three scalars.
method Solve(n: int, a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 5
{
  output := IntToString(if n - a < b + 1 then n - a else b + 1);
  steps := 5;
}
