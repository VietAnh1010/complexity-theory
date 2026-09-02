// p02899 AtCoder Beginner Contest 142 - Go to School  (problem 1421, solution 1421_53)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N = int(input())
// A = [int(i) for i in input().split()]
// B=[0]*N
// for i in range(N):
//   B[A[i]-1]=i+1
// print(*B)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var b := seq(n, i => 0);
  var i := 0;
  while i < n
    decreases n - i
  {
    b := b[(a_list[i]-1) := i+1];
    i := i + 1;
  }
  output := JoinInts(b, " ");
}
