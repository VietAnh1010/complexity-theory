// 361_B. Levko and Permutation  (problem 2089, solution 2089_121)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// if n==k:
//     print(-1)
// else:
//     a=[]
//     a.append(n-k)
//     for i in range(1,n-k):
//         a.append(i)
//     for j in range(n-k+1,n+1):
//         a.append(j)
//     print(*a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  if a == b {
    output := "-1\n";
  } else {
    var lst: seq<int> := [a - b];
    var i := 1;
    while i < a - b
    {
      lst := lst + [i];
      i := i + 1;
    }
    var j := a - b + 1;
    while j <= a
    {
      lst := lst + [j];
      j := j + 1;
    }
    output := JoinInts(lst, " ") + "\n";
  }
}
