// 1108_A. Two distinct points  (problem 936, solution 936_203)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for a in range(n):
//     L=list(map(int,input().split()))
//     if(L[0]==L[2]):
//         print(L[0],L[2]+1)
//     else:
//         print(L[0],L[2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, grid: seq<seq<int>>) returns (output: string)
  requires forall r :: r in grid ==> |r| >= 3
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |grid|
    invariant 0 <= i
    decreases n - i
  {
    var row := grid[i];
    if row[0] == row[2] {
      parts := parts + [IntToString(row[0]) + " " + IntToString(row[2] + 1) + "\n"];
    } else {
      parts := parts + [IntToString(row[0]) + " " + IntToString(row[2]) + "\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
