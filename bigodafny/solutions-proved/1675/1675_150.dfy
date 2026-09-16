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

method Solve(v0: string, v1: string) returns (output: string, ghost steps: nat)
  ensures steps <= 60 * |v0| + 60 * |v1| + 200
{
  steps := 1;
  var s := v0;
  var t := v1;
  var c := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant steps == 4 * i + 1
    decreases |s| - i
  {
    if c < |t| && t[c] == s[i] { c := c + 1; }
    i := i + 1;
    steps := steps + 4;
  }
  if c == |t| {
    output := "automaton";
    steps := steps + 1;
  } else {
    var eqAll := true;
    var geAll := true;
    var k := 0;
    while k < 26
      invariant 0 <= k <= 26
      // each iteration charges a call to CountChar1675 on s and on t: a
      // recursive prelude-style function over a string costs its length.
      invariant steps == 4 * |s| + 1 + k * (|s| + |t| + 4)
      decreases 26 - k
    {
      var ch := (('a' as int) + k) as char;
      var ac := CountChar1675(s, ch);
      var bc := CountChar1675(t, ch);
      steps := steps + |s| + |t|;
      if ac != bc { eqAll := false; }
      if ac < bc { geAll := false; }
      k := k + 1;
      steps := steps + 4;
    }
    if eqAll {
      output := "array";
    } else if geAll {
      output := "both";
    } else {
      output := "need tree";
    }
    steps := steps + 1;
  }
}
