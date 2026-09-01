// 448_B. Suffix Structures  (problem 1675, solution 1675_150)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input().strip()
// t=input().strip()
// a=[s.count(chr(ord('a')+i))for i in range(26)]
// b=[t.count(chr(ord('a')+i))for i in range(26)]
// c=0
// for i in s:
//     if (c < len(t) and t[c] == i):
//         c+= 1
// if (c == len(t)):
//     print("automaton")
// elif all(a[i] == b[i] for i in range(26)):
//     print("array")
// elif all(a[i] >= b[i] for i in range(26)):
//     print("both")
// else:
//     print("need tree")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountChar1675(s: string, ch: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == ch then 1 else 0) + CountChar1675(s[1..], ch)
}

method Solve(v0: string, v1: string) returns (output: string)
{
  var s := v0;
  var t := v1;
  var c := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if c < |t| && t[c] == s[i] { c := c + 1; }
    i := i + 1;
  }
  if c == |t| {
    output := "automaton";
  } else {
    var eqAll := true;
    var geAll := true;
    var k := 0;
    while k < 26
      decreases 26 - k
    {
      var ch := (('a' as int) + k) as char;
      var ac := CountChar1675(s, ch);
      var bc := CountChar1675(t, ch);
      if ac != bc { eqAll := false; }
      if ac < bc { geAll := false; }
      k := k + 1;
    }
    if eqAll {
      output := "array";
    } else if geAll {
      output := "both";
    } else {
      output := "need tree";
    }
  }
}
