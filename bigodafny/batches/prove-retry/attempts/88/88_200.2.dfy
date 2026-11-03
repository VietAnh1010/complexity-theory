include "../../../../prelude.dfy"

lemma ReverseStepsBound(s: string)
  ensures ReverseString_steps(s) <= 7 * |s| + 3
  decreases |s|
{
  if |s| > 0 { ReverseStepsBound(s[1..]); }
}

method Solve(n: int, string_list: seq<string>)
    returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |string_list| == 2 * n
  ensures steps <= 31 * n + 20 * SumLen(string_list) + 2 * |output| + 1
{
  steps := 0;
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |parts| == t
    invariant steps <= 30 * t + 20 * SumLen(string_list[..2 * t]) + SumLen(parts)
    decreases n - t
  {
    ghost var s0 := steps;
    steps := steps + 2;
    ReverseStepsBound(string_list[2 * t]);
    ReverseStepsBound(string_list[2 * t + 1]);
    steps := steps + (2 + ReverseString_steps(string_list[2 * t]));
    var x := ReverseString(string_list[2 * t]);
    steps := steps + (3 + ReverseString_steps(string_list[2 * t + 1]));
    var y := ReverseString(string_list[2 * t + 1]);
    ReverseLen(string_list[2 * t]);
    ReverseLen(string_list[2 * t + 1]);
    var a := 0;
    var i := 0;
    var found := false;
    ghost var s1 := steps;
    while i < |y| && !found
      invariant 0 <= i <= |y|
      invariant steps <= s1 + 9 * i
      decreases |y| - i
    {
      steps := steps + (4 + if i < |y| then 1 else 0);
      steps := steps + 2;
      if y[i] == '1' {
        steps := steps + 1;
        a := i + 1;
        found := true;
      }
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + (3 + if i < |y| then 1 else 0);
    var b := 0;
    var j := 0;
    var found2 := false;
    ghost var s2 := steps;
    while j < |x| && !found2
      invariant 0 <= j <= |x|
      invariant steps <= s2 + 12 * j
      decreases |x| - j
    {
      steps := steps + (4 + if j < |x| then 1 else 0);
      steps := steps + (3 + if x[j] == '1' then 2 else 0);
      if x[j] == '1' && j + 1 >= a {
        steps := steps + 1;
        b := j + 1;
        found2 := true;
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + (3 + if j < |x| then 1 else 0);
    IntToStringDigits(b - a);
    steps := steps + (2 + Digits(b - a) + |[IntToString(b - a)]|);
    SumLenSnoc(parts, IntToString(b - a));
    parts := parts + [IntToString(b - a)];
    steps := steps + 1;
    assert string_list[..2 * t + 1] == string_list[..2 * t] + [string_list[2 * t]];
    assert string_list[..2 * t + 2] == string_list[..2 * t + 1] + [string_list[2 * t + 1]];
    SumLenSnoc(string_list[..2 * t], string_list[2 * t]);
    SumLenSnoc(string_list[..2 * t + 1], string_list[2 * t + 1]);
    t := t + 1;
  }
  assert string_list[..2 * t] == string_list;
  steps := steps + 1;
  steps := steps + (SumLen(parts) + |parts|);
  output := Join(parts, "\n");
  if |parts| >= 1 { JoinLen(parts, "\n"); }
}

function ReverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then
    s
  else
    ReverseString(s[1..]) + [s[0]]
}

lemma ReverseLen(s: string)
  ensures |ReverseString(s)| == |s|
  decreases |s|
{
  if |s| > 0 { ReverseLen(s[1..]); }
}

ghost function ReverseString_steps(s: string): nat
  decreases |s|
{
  3 + if |s| == 0 then 0 else 3 + ReverseString_steps(s[1..]) + |[s[0]]|
}

import opened Prelude
