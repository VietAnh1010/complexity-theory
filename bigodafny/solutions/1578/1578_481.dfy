// 1236_A. Stones  (problem 1578, solution 1578_481)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for i in range(t):
//     a,b,c=map(int,input().split())
//     n=min(b,c//2)
//     b-=n
//     m=min(a,b//2)
//     print((m+n)*3)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| >= 3
{
  var parts: seq<string> := [];
  var idx := 0;
  while idx < |matrix|
    invariant 0 <= idx <= |matrix|
    decreases |matrix| - idx
  {
    var a := matrix[idx][0];
    var b := matrix[idx][1];
    var c := matrix[idx][2];
    var nn := if b < FloorDiv(c, 2) then b else FloorDiv(c, 2);
    b := b - nn;
    var m := if a < FloorDiv(b, 2) then a else FloorDiv(b, 2);
    parts := parts + [IntToString((m + nn) * 3) + "\n"];
    idx := idx + 1;
  }
  output := Join(parts, "");
}
