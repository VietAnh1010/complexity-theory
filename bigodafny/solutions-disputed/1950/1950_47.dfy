// TRANSLATION AUDIT -- queued for manual review, not a decision.
//
//   gate            : validate.py records `fail`  (19/42 tests)
//   harness ceiling : 23/42. The problem's Input dataclass types the
//                     coefficient as `float`, and these inputs carry up to 100
//                     significant digits. 19 of the 42 stored tests do not
//                     survive `str(float(c)) + 'e' + str(int(e))`, so the
//                     ORIGINAL PYTHON fails them too once routed through the
//                     dataclass. No translation can pass those 19.
//   genuine failures: at least 4 of the 23 runnable tests. The Dafny
//                     passes 19; the Python through the same round-trip
//                     passes 23.
//   cause           : translation
//   control         : batches/gate-audit/control.py, 2026-09-21
//   note            : filed here as the review queue, not as a label dispute.
//                     What is disputed is the code. Moving it back to
//                     solutions/ needs 23/23 on the runnable tests plus an
//                     entry in data/gate_exempt.jsonl for the other 19.
//
// 697_B. Barnicle  (problem 1950, solution 1950_47)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from decimal import *
// 
// while True :
//     try :
//         a=input()
//         b=Decimal(a)
// 
//         if(round(b)==b):
//             print ("%d"%b)
//         else:
//             print (b)
//     
//     except :
//         break
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(coefficient: real, exponent: int) returns (output: string)
{
  var neg := coefficient < 0.0;
  var ac := if neg then -coefficient else coefficient;
  var pow: real := 1.0;
  var e := exponent;
  if e >= 0 {
    var t := 0;
    while t < e { pow := pow * 10.0; t := t + 1; }
  } else {
    var t := 0;
    while t < -e { pow := pow / 10.0; t := t + 1; }
  }
  var value := ac * pow;
  var iv := value.Floor;
  if (iv as real) == value {
    output := (if neg && iv != 0 then "-" else "") + IntToString(iv) + "\n";
  } else {
    var scaled := (value * 1000000000000.0).Floor;
    var digits := IntToString(scaled);
    while |digits| < 13 { digits := "0" + digits; }
    var intStr := digits[..|digits|-12];
    var fracStr0 := digits[|digits|-12..];
    var fl := |fracStr0|;
    while fl > 0 && fracStr0[fl-1] == '0'
      invariant 0 <= fl <= |fracStr0|
    { fl := fl - 1; }
    var fracStr := fracStr0[..fl];
    output := (if neg then "-" else "") + intStr + (if |fracStr| > 0 then "." + fracStr else "") + "\n";
  }
}
