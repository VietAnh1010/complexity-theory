// 1091_B. New Year and the Treasure Geolocation  (problem 2185, solution 2185_274)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = 0
// b = 0
// for _ in range(2*n):
// 	x,y = map(int,input().split(" "))
// 	a += x
// 	b += y
// print(a//n,b//n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coord_list: seq<seq<int>>) returns (output: string)
  requires n != 0
  requires forall k :: 0 <= k < |coord_list| ==> |coord_list[k]| >= 2
{
  var a := 0;
  var b := 0;
  var i := 0;
  while i < |coord_list|
    invariant 0 <= i <= |coord_list|
    decreases |coord_list| - i
  {
    a := a + coord_list[i][0];
    b := b + coord_list[i][1];
    i := i + 1;
  }
  output := IntToString(FloorDiv(a, n)) + " " + IntToString(FloorDiv(b, n));
}
