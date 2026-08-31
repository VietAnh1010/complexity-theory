// 281_B. Nearest Fraction  (problem 696, solution 696_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import inf,floor,ceil
// x,y,n=map(float,input().split())
// m=inf
// ans=""
// for b in range(1,int(n+1)):
//     a=floor((x*b)/y)
//     z=abs(x/y-a/b)
//     if z<m-1e-15:
//         m=z
//         ans=str(a)+'/'+str(b)
//     a=ceil((x*b)/y)
//     z=abs(x/y-a/b)
//     if z<m-1e-15:
//         m=z
//         ans=str(a)+'/'+str(b)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: int, v_2: int) returns (output: string)
{
  var x := v_0; var y := v_1; var n := v_2;
  var hasAns := false;
  var mNum := 0; var mDen := 1;
  var ans := "";
  var b := 1;
  while b <= n
    decreases n - b
  {
    var a1 := FloorDiv(x * b, y);
    var z1n := AbsInt(x * b - a1 * y);
    var z1d := y * b;
    if !hasAns || z1n * mDen < mNum * z1d {
      hasAns := true;
      mNum := z1n; mDen := z1d;
      ans := IntToString(a1) + "/" + IntToString(b);
    }
    var a2 := FloorDiv(x * b + y - 1, y);
    var z2n := AbsInt(x * b - a2 * y);
    var z2d := y * b;
    if !hasAns || z2n * mDen < mNum * z2d {
      hasAns := true;
      mNum := z2n; mDen := z2d;
      ans := IntToString(a2) + "/" + IntToString(b);
    }
    b := b + 1;
  }
  output := ans;
}
