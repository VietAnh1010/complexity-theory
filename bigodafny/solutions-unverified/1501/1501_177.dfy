// 1177_A. Digits Sequence (Easy Edition)  (problem 1501, solution 1501_177)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// print(''.join(str(x) for x in range(1, 2778))[int(input()) -1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// digit count of x, for the range this row builds
ghost function DigitBand(x: int): nat
{
  if x < 10 then 1 else if x < 100 then 2 else if x < 1000 then 3 else 4
}

// 9*1 + 90*2 + 900*3 + 1778*4 == 10001, measured one uniform band at a time.
lemma LenOf1To2777(parts: seq<string>)
  requires |parts| == 2777
  requires forall k :: 0 <= k < |parts| ==> |parts[k]| == DigitBand(k + 1)
  ensures |Join(parts, "")| == 10001
{
  var a, b, c, d := parts[..9], parts[9..99], parts[99..999], parts[999..];
  assert parts == a + (b + (c + d));
  JoinSplitEmptySep(a, b + (c + d));
  JoinSplitEmptySep(b, c + d);
  JoinSplitEmptySep(c, d);
  JoinLenUniform(a, 1);
  JoinLenUniform(b, 2);
  JoinLenUniform(c, 3);
  JoinLenUniform(d, 4);
}

method Solve(n: int) returns (output: string)
  // 10001 is the exact length of "1".."2777" concatenated, proved below.
  // 91 of 212 stored inputs exceed it; every one of those raises IndexError
  // in the row's own Python, so there is no behaviour there to reproduce.
  requires 1 <= n <= 10001
{
  var parts: seq<string> := [];
  var x := 1;
  while x < 2778
    invariant 1 <= x <= 2778
    invariant |parts| == x - 1
    invariant forall k :: 0 <= k < |parts| ==> |parts[k]| == DigitBand(k + 1)
    decreases 2778 - x
  {
    IntToStringLen(x);
    parts := parts + [IntToString(x)];
    x := x + 1;
  }
  LenOf1To2777(parts);
  var s := Join(parts, "");
  assert |s| == 10001;
  output := [s[n - 1]] + "\n";
}
