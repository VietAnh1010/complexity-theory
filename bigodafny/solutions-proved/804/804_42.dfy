// 858_B. Which floor?  (problem 804, solution 804_42)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// a = [0] * m
// for i in range(m):
//     a[i] = list(map(int, input().split()))
//     a[i][0] -= 1
//     a[i][1] -= 1
// 
// n -= 1
// canbe = set()
// 
// last = 0
// 
// for i in range(1, 200):
//     good = 1
//     for j in range(m):
//         k = a[j][0]
//         f = a[j][1]
//         if not (i * f <= k <= i * (f + 1) - 1):
//             good = 0
//     if good:
//         canbe.add(n // i)
//         last = n // i + 1
// 
// if len(canbe) == 1:
//     print(last)
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n_nodes: int, n_edges: int, edges: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n_edges <= |edges|
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| == 2
  ensures steps <= 2000 * (if n_edges > 0 then n_edges else 0) + 3000 + |output|
{
  steps := 1;
  var n := n_nodes - 1;
  var canbe: set<int> := {};
  var last := 0;
  var i := 1;
  ghost var E: nat := if n_edges > 0 then n_edges else 0;
  ghost var L: nat := 10 * E + 10;
  steps := steps + 3;
  while i < 200
    invariant 1 <= i <= 200
    invariant steps <= 4 + (i - 1) * L
    decreases 200 - i
  {
    var good := true;
    var j := 0;
    ghost var st := steps;
    while j < n_edges
      invariant 0 <= j <= E
      invariant steps == st + 10 * j
      decreases n_edges - j
    {
      var k := edges[j][0] - 1;
      var f := edges[j][1] - 1;
      if !(i * f <= k && k <= i * (f + 1) - 1) {
        good := false;
      }
      j := j + 1;
      steps := steps + 10;
    }
    if good {
      canbe := canbe + {n / i};
      last := n / i + 1;
    }
    steps := steps + 10;
    CostMulDistrib(i - 1, 1, i, L);
    i := i + 1;
  }
  if |canbe| == 1 {
    output := IntToString(last) + "\n";
    IntToStringDigits(last);
    steps := steps + 3 + Digits(last) + 1;
  } else {
    output := "-1\n";
    steps := steps + 3 + |output|;
  }
}
