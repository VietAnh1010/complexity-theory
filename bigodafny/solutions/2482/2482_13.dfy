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

lemma MulAtLeast(n: int, a: int)
  requires n >= 0 && a >= 1
  ensures n * a >= n
{
  assert n * a == n * (a - 1) + n;
  assert n * (a - 1) >= 0;
}

method Solve(N: int, M: int) returns (output: string)
  requires N >= 2
{
  var n := 0;
  while n * (N - 1) + 1 < M
    invariant n >= 0
    decreases M - n
  {
    MulAtLeast(n, N - 1);
    n := n + 1;
  }
  output := IntToString(n);
}
