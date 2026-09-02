// 858_B. Which floor?  (problem 804, solution 804_10)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split(' '))
// n -= 1
// if m == 0:
//     if n == 0:
//         print(1)
//     else:
//         print(-1)
//     exit(0)
// 
// minAps = 0
// maxAps = 100000
// for i in range(m):
//     k, f = map(int, input().split(' '))
//     k -= 1
//     f -= 1
//     if f == 0:
//         minAps = max(minAps, k + 1)
//     else:
//         minAps = max(minAps, 1 + k // (f + 1))
//         maxAps = min(maxAps, k // f)
// 
// minFloor = n // maxAps
// maxFloor = n // minAps
// if minFloor == maxFloor:
//     print(minFloor + 1)
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n_nodes: int, n_edges: int, edges: seq<seq<int>>) returns (output: string)
{
  var n := n_nodes - 1;
  if n_edges == 0 {
    if n == 0 {
      output := "1\n";
    } else {
      output := "-1\n";
    }
  } else {
    var minAps := 0;
    var maxAps := 100000;
    var i := 0;
    while i < n_edges
      decreases n_edges - i
    {
      var k := edges[i][0] - 1;
      var f := edges[i][1] - 1;
      if f == 0 {
        if k + 1 > minAps { minAps := k + 1; }
      } else {
        var cand := 1 + k / (f + 1);
        if cand > minAps { minAps := cand; }
        var cand2 := k / f;
        if cand2 < maxAps { maxAps := cand2; }
      }
      i := i + 1;
    }
    var minFloor := n / maxAps;
    var maxFloor := n / minAps;
    if minFloor == maxFloor {
      output := IntToString(minFloor + 1) + "\n";
    } else {
      output := "-1\n";
    }
  }
}
