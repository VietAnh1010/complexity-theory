// 1205_A. Almost Equal  (problem 1015, solution 1015_168)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = [0 for i in range(2*n+1)]
// if n%2 == 0:
//     print('NO')
// else:
//     toggle = True
//     for i in range(1,n+1):
//         if toggle:
//             l[i] = 2*i-1
//             l[i+n] = 2*i
//             toggle = False
//         else:
//             l[i] = 2*i
//             l[i+n] = 2*i -1
//             toggle = True
//     print('YES')
//     for i in range(1,2*n +1):
//         print(l[i],end = " ")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 6 * n + 4
{
  steps := 1;
  if n % 2 == 0 {
    output := "NO";
  } else {
    var partA: seq<int> := [];
    var partB: seq<int> := [];
    var toggle := true;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant |partA| == i - 1
      invariant |partB| == i - 1
      invariant steps <= 3 * (i - 1) + 1
      decreases n - i + 1
    {
      if toggle {
        partA := partA + [2 * i - 1];
        partB := partB + [2 * i];
        toggle := false;
      } else {
        partA := partA + [2 * i];
        partB := partB + [2 * i - 1];
        toggle := true;
      }
      i := i + 1;
      steps := steps + 3;
    }
    var joined := partA + partB;
    steps := steps + |partB|;
    output := "YES\n" + JoinInts(joined, " ");
    steps := steps + |joined| + 1;
  }
}
