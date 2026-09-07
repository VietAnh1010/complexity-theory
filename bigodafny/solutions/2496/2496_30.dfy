// 442_B. Andrey and Problem  (problem 2496, solution 2496_30)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// input()
// ps = sorted((float(p) for p in input().split()), reverse=True)
// if 1.0 in ps:
//     print(1)
//     sys.exit()
// a, b = 0, 1
// for p in ps:
//     c, d = a + p / (1 - p), b * (1 - p)
//     if c * d > a * b:
//         a, b = c, d
//     else:
//         break
// print('{:.9}'.format(a * b))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method FormatG9(value: real) returns (s: string)
{
  if value == 0.0 {
    s := "0";
    return;
  }
  var neg := value < 0.0;
  var v := if neg then -value else value;
  var e := 0;
  var iter := 0;
  while v >= 10.0 && iter < 1000
    invariant 0 <= iter <= 1000
    decreases 1000 - iter
  {
    v := v / 10.0;
    e := e + 1;
    iter := iter + 1;
  }
  iter := 0;
  while v < 1.0 && iter < 1000
    invariant 0 <= iter <= 1000
    decreases 1000 - iter
  {
    v := v * 10.0;
    e := e - 1;
    iter := iter + 1;
  }
  var scaled := v * 100000000.0;
  var digits := (scaled + 0.5).Floor;
  if digits >= 1000000000 {
    digits := digits / 10;
    e := e + 1;
  }
  var digitStr := IntToString(digits);
  while |digitStr| < 9
  {
    digitStr := "0" + digitStr;
  }
  var trimEnd := |digitStr|;
  while trimEnd > 1 && digitStr[trimEnd-1] == '0'
    invariant 1 <= trimEnd <= |digitStr|
  {
    trimEnd := trimEnd - 1;
  }
  var trimmed := digitStr[..trimEnd];
  assert |trimmed| >= 1;

  var body: string;
  if e < -4 || e >= 9 {
    var mantissa := if |trimmed| == 1 then trimmed else trimmed[..1] + "." + trimmed[1..];
    var expSign := if e < 0 then "-" else "+";
    var expAbs := if e < 0 then -e else e;
    var expStr := IntToString(expAbs);
    while |expStr| < 2
    {
      expStr := "0" + expStr;
    }
    body := mantissa + "e" + expSign + expStr;
  } else if e >= 0 {
    var intLen := e + 1;
    if intLen >= |trimmed| {
      body := trimmed + Repeat("0", intLen - |trimmed|);
    } else {
      body := trimmed[..intLen] + "." + trimmed[intLen..];
    }
  } else {
    body := "0." + Repeat("0", -e - 1) + trimmed;
  }
  s := (if neg then "-" else "") + body;
}

method Solve(n: int, a_list: seq<real>) returns (output: string)
  requires |a_list| == n
{
  var ps := Sort(a_list, (x: real, y: real) => x > y);
  var hasOne := false;
  var i := 0;
  while i < |ps|
    invariant 0 <= i <= |ps|
    invariant !hasOne ==> forall k :: 0 <= k < i ==> ps[k] != 1.0
  {
    if ps[i] == 1.0 { hasOne := true; }
    i := i + 1;
  }
  if hasOne {
    output := "1\n";
  } else {
    assert forall k :: 0 <= k < |ps| ==> ps[k] != 1.0;
    var a: real := 0.0;
    var b: real := 1.0;
    var stopped := false;
    i := 0;
    while i < |ps| && !stopped
      invariant 0 <= i <= |ps|
      invariant forall k :: 0 <= k < |ps| ==> ps[k] != 1.0
    {
      var p := ps[i];
      var c := a + p / (1.0 - p);
      var d := b * (1.0 - p);
      if c * d > a * b {
        a := c;
        b := d;
      } else {
        stopped := true;
      }
      i := i + 1;
    }
    var res := FormatG9(a * b);
    output := res + "\n";
  }
}
