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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires n <= |a_list|
  requires forall k :: 0 <= k < n ==> -n <= a_list[k] - 1 < n
  ensures steps <= 4 * n + 2
{
  steps := 1;
  var b := seq(n, i => 0);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |b| == n
    invariant steps <= 3 * i + 1
    decreases n - i
  {
    b := b[PyIndex(a_list[i] - 1, |b|) := i+1];
    i := i + 1;
    steps := steps + 3;
  }
  output := JoinInts(b, " ");
  steps := steps + |b| + 1;
}
