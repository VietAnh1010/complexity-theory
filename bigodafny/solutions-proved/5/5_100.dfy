// 622_A. Infinite Sequence  (problem 5, solution 5_100)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// k=1
// while(n>k):
//    n-=k
//    k+=1
// print(n)
//    
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 2 * n + 3
{
  steps := 1;
  var m, k := n, 1;
  while m > k
    invariant 1 <= m <= n
    invariant k >= 1
    invariant steps <= 2 * (n - m) + 1
    decreases m - k
  {
    m := m - k;
    k := k + 1;
    steps := steps + 2;
  }
  output := IntToString(m) + "\n";
  steps := steps + 1;
}
