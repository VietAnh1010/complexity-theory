// 281_B. Nearest Fraction  (problem 696, solution 696_49)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from fractions import Fraction
// 
// x,y,n = map(int, input().split(" "))
// f=Fraction(x,y).limit_denominator(n)
// a=f.numerator
// b=f.denominator
// print(str(a)+"/"+str(b))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: int, v_2: int) returns (output: string)
{
  var x0 := v_0; var y0 := v_1; var maxDen := v_2;
  var g := Gcd(AbsInt(x0), AbsInt(y0));
  var xn: int; var yd: int;
  if g == 0 {
    xn := x0; yd := y0;
  } else {
    xn := x0 / g; yd := y0 / g;
  }
  var a: int; var b: int;
  if yd <= maxDen {
    a := xn; b := yd;
  } else {
    var p0 := 0; var q0 := 1; var p1 := 1; var q1 := 0;
    var n := xn; var d := yd;
    var fuel := yd + 1;
    var doneFlag := false;
    while !doneFlag && fuel > 0
      decreases fuel
    {
      if d == 0 {
        doneFlag := true;
      } else {
        var k := FloorDiv(n, d);
        var q2 := q0 + k * q1;
        if q2 > maxDen {
          doneFlag := true;
        } else {
          var np1 := p0 + k * p1;
          var nd := n - k * d;
          p0 := p1; q0 := q1; p1 := np1; q1 := q2;
          n := d; d := nd;
        }
      }
      fuel := fuel - 1;
    }
    if q1 == 0 {
      a := xn; b := yd;
    } else {
      var kk := FloorDiv(maxDen - q0, q1);
      var bound1Num := p0 + kk * p1;
      var bound1Den := q0 + kk * q1;
      var bound2Num := p1;
      var bound2Den := q1;
      var diff2Num := AbsInt(bound2Num * yd - bound2Den * xn);
      var diff2Den := bound2Den * yd;
      var diff1Num := AbsInt(bound1Num * yd - bound1Den * xn);
      var diff1Den := bound1Den * yd;
      if diff2Num * diff1Den <= diff1Num * diff2Den {
        a := bound2Num; b := bound2Den;
      } else {
        a := bound1Num; b := bound1Den;
      }
    }
  }
  output := IntToString(a) + "/" + IntToString(b);
}
