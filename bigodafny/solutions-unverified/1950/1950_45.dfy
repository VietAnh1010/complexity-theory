// 697_B. Barnicle  (problem 1950, solution 1950_45)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a, b = input().split('e')
// b = int(b)
// pos = a.find('.') + b
// a = ''.join(a.split('.'))
// a = list(a)
// while len(a) < pos:
//     a.append('0')
// a = ''.join(a[:pos]) + '.' + ''.join(a[pos:])
// if len(a) == pos + 1: a = a[:-1]
// elif len(a) > 2 and a[-2:] == '.0': a = a[:-2]
// print(a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(coefficient: real, exponent: int) returns (output: string)
{
  var sign := if coefficient < 0.0 then "-" else "";
  var ac := if coefficient < 0.0 then -coefficient else coefficient;
  var scaled := (ac * 1000000000000.0).Floor;
  var digits := IntToString(scaled);
  while |digits| < 13
  {
    digits := "0" + digits;
  }
  var intStr := digits[..|digits|-12];
  var fracStr0 := digits[|digits|-12..];
  var fl := |fracStr0|;
  while fl > 0 && fracStr0[fl-1] == '0'
  {
    fl := fl - 1;
  }
  var fracStr := fracStr0[..fl];
  var a := sign + (if |fracStr| == 0 then intStr else intStr + "." + fracStr);
  var b := exponent;
  var dotIdx := -1;
  var di := 0;
  while di < |a|
  {
    if a[di] == '.' { dotIdx := di; }
    di := di + 1;
  }
  var pos := dotIdx + b;
  var joined := "";
  var ji := 0;
  while ji < |a|
  {
    if a[ji] != '.' { joined := joined + [a[ji]]; }
    ji := ji + 1;
  }
  var arr := joined;
  var effPos := if pos < 0 then 0 else pos;
  while |arr| < effPos
  {
    arr := arr + "0";
  }
  var res := arr[..effPos] + "." + arr[effPos..];
  if |res| == effPos + 1 {
    res := res[..|res|-1];
  } else if |res| > 2 && res[|res|-2..] == ".0" {
    res := res[..|res|-2];
  }
  output := res + "\n";
}
