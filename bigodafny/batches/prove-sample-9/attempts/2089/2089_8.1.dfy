// 361_B. Levko and Permutation  (problem 2089, solution 2089_8)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// n,k=map(int,input().split())
// if n<=k:
//     print(-1)
// else:
//     l=[n-k]
//     for i in range(2,n-k+1):
//         l.append(i-1)
//     for i in range(n-k+1,n+1):
//         l.append(i)
//     print(*l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 5 * (if a > b then a - b else 0) + 4 * (if b > 0 && a > b then b else 0) + 12 + 2 * |output|
{
  steps := 2;
  if a <= b {
    output := "-1\n";
    steps := steps + 1;
  } else {
    var lst: seq<int> := [a - b];
    var i := 2;
    steps := steps + 4;
    var mb := if b > 0 then b else 0;
    while i <= a - b
      invariant 2 <= i <= a - b + 1
      invariant |lst| == i - 1
      invariant steps <= 6 + 5 * (i - 2)
      decreases a - b + 1 - i
    {
      lst := lst + [i-1];
      i := i + 1;
      steps := steps + 5;
    }
    var j := a - b + 1;
    steps := steps + 2;
    while j <= a
      invariant a - b + 1 <= j <= a - b + 1 + mb
      invariant |lst| == j - 1 - (if j > a - b + 1 then 0 else 0)
      invariant steps <= 8 + 5 * (a - b - 1) + 4 * (j - (a - b + 1))
      decreases a + 1 - j
    {
      lst := lst + [j];
      j := j + 1;
      steps := steps + 4;
    }
    output := JoinInts(lst, " ") + "\n";
    JoinIntsLen(lst, " ");
    steps := steps + SumDigits(lst) + |lst| + 1;
  }
}
