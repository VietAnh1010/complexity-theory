// 621_B. Wet Shark and Bishops  (problem 750, solution 750_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// 
// a = [0] * 2001
// b = [0] * 2001
// for i in range(n):
//     x, y = map(int, input().split())
//     a[x - y] += 1
//     b[x + y] += 1
// 
// ans = 0
// for i in range(2001):
//     ans += a[i] * (a[i] - 1) // 2
//     ans += b[i] * (b[i] - 1) // 2
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data_points: seq<(int, int)>) returns (output: string)
{
  var aArr := new int[2001];
  var bArr := new int[2001];
  var i := 0;
  while i < |data_points|
    decreases |data_points| - i
  {
    var x := data_points[i].0;
    var y := data_points[i].1;
    var idxA := FloorMod(x - y, 2001);
    var idxB := FloorMod(x + y, 2001);
    aArr[idxA] := aArr[idxA] + 1;
    bArr[idxB] := bArr[idxB] + 1;
    i := i + 1;
  }
  var ans := 0;
  i := 0;
  while i < 2001
    decreases 2001 - i
  {
    ans := ans + aArr[i]*(aArr[i]-1)/2;
    ans := ans + bArr[i]*(bArr[i]-1)/2;
    i := i + 1;
  }
  output := IntToString(ans);
}
