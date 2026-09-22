// 998_A. Balloons  (problem 2225, solution 2225_120)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(i) for i in input().split()]
// res = []
// if n == 2 and a[0] == a[1]:
//     print("-1")
// elif n == 1:
//     print("-1")
// else:
//     for i in range(n):
//         if a[i] != sum(a)-a[i]:
//             #print("1")
//             res.append(i+1)
//             break
// if len(res)!=0:
//     print("1")
//     print(*res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, dimensions: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |dimensions| == n
  ensures steps <= 4 * n + |output| + 8
{
  steps := 1;
  var a := dimensions;
  if (n == 2 && a[0] == a[1]) || n == 1 {
    output := "-1\n";
    steps := steps + 2;
  } else {
    var total := SumSeq(a);
    steps := steps + n + 1;
    var idx := -1;
    var i := 0;
    ghost var base1 := steps;
    while i < n && idx == -1
      invariant 0 <= i <= n
      invariant steps <= base1 + 3 * i
    {
      if a[i] != total - a[i] {
        idx := i;
      }
      i := i + 1;
      steps := steps + 3;
    }
    assert steps <= base1 + 3 * n;
    if idx != -1 {
      output := "1\n" + IntToString(idx + 1) + "\n";
    } else {
      output := "";
    }
    steps := steps + |output| + 3;
  }
}
