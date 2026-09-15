// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(logn)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop implements a continued-fraction search (p0/q0/p1/q1,
//     k := FloorDiv(n,d)) whose iteration count is the number of
//     continued-fraction terms of x0/y0, an O(log(y0)) Euclidean-style
//     bound rather than a fixed constant; Python's
//     Fraction(x,y).limit_denominator(n) performs the same
//     continued-fraction expansion internally, so O(1) undercounts both
//     sides, though I am not fully certain the dataset doesn't intend O(1)
//     loosely here.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 60, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString"], "loop_depth":
//     1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 0,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
