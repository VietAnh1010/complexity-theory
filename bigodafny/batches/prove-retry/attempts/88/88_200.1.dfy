include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_list: seq<string>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |string_list| == 2 * n
  ensures steps <= 42 * n + 30 * SumLen(string_list) + 2 * |output| + 4
{
  steps := 2;
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |parts| == t
    invariant steps <= 2 + 41 * t + 30 * SumLen(string_list[..2 * t]) + SumLen(parts)
    decreases n - t
  {
    ghost var s0 := steps;
    ReverseLen(string_list[2 * t]);
    ReverseLen(string_list[2 * t + 1]);
    var x := ReverseString(string_list[2 * t]);
    var y := ReverseString(string_list[2 * t + 1]);
    steps := steps + |x| + |y| + 2;
    var a := 0;
    var i := 0;
    var found := false;
    ghost var s1 := steps;
    while i < |y| && !found
      invariant 0 <= i <= |y|
      invariant steps <= s1 + 10 * i
      decreases |y| - i
    {
      steps := steps + 10;
      if y[i] == '1' {
        a := i + 1;
        found := true;
      }
      i := i + 1;
    }
    var b := 0;
    var j := 0;
    var found2 := false;
    ghost var s2 := steps;
    while j < |x| && !found2
      invariant 0 <= j <= |x|
      invariant steps <= s2 + 10 * j
      decreases |x| - j
    {
      steps := steps + 10;
      if x[j] == '1' && j + 1 >= a {
        b := j + 1;
        found2 := true;
      }
      j := j + 1;
    }
    IntToStringDigits(b - a);
    steps := steps + Digits(b - a) + 6;
    SumLenSnoc(parts, IntToString(b - a));
    parts := parts + [IntToString(b - a)];
    assert string_list[..2 * t + 1] == string_list[..2 * t] + [string_list[2 * t]];
    assert string_list[..2 * t + 2] == string_list[..2 * t + 1] + [string_list[2 * t + 1]];
    SumLenSnoc(string_list[..2 * t], string_list[2 * t]);
    SumLenSnoc(string_list[..2 * t + 1], string_list[2 * t + 1]);
    t := t + 1;
  }
  assert string_list[..2 * t] == string_list;
  output := Join(parts, "\n");
  if |parts| >= 1 { JoinLen(parts, "\n"); }
  steps := steps + SumLen(parts) + |parts|;
}

function ReverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then s else ReverseString(s[1..]) + [s[0]]
}

lemma ReverseLen(s: string)
  ensures |ReverseString(s)| == |s|
  decreases |s|
{
  if |s| > 0 { ReverseLen(s[1..]); }
}
