// 998_A. Balloons  (problem 2225, solution 2225_154)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// z=sorted(l)
// for i in range(n):
//   if(l[i]==z[0]):
//     mi=i
// if(n>2):
//   print(1)
//   print(mi+1)
// else:
//   if(n==2):
//     if(l[0]==l[1]):
//       print(-1)
//     else:
//       print(1)
//       print(1)
//   else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, dimensions: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |dimensions| == n
  ensures steps <= 2 * NLogN(n) + 2 * n + 6
{
  var l := dimensions;
  SortCostNLogN(n);
  var z := SortInts(l);
  steps := 1 + SortCost(n);
  var minVal := z[0];
  var mi := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + SortCost(n) + 2 * i
  {
    if l[i] == minVal {
      mi := i;
    }
    i := i + 1;
    steps := steps + 2;
  }
  if n > 2 {
    output := "1\n" + IntToString(mi + 1) + "\n";
  } else if n == 2 {
    if l[0] == l[1] {
      output := "-1\n";
    } else {
      output := "1\n1\n";
    }
  } else {
    output := "-1\n";
  }
  steps := steps + 3;
}
