// p02922 AtCoder Beginner Contest 139 - Power Socket  (problem 2482, solution 2482_13)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// n=0
// while n*(a-1)+1<b:n+=1
// print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, M: int) returns (output: string)
  decreases *
{
  var n := 0;
  while n * (N - 1) + 1 < M
    decreases *
  {
    n := n + 1;
  }
  output := IntToString(n);
}
