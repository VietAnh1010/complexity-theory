// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
//     n = input()
//     k = len(n.replace('0', ''))
//     print(k)
//     ln = len(n)
//     lst = [n[i]+'0'*(ln-i-1) for i in range(ln) if n[i] != '0']
//     print(*lst)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma RepeatLen0(k: nat)
  ensures |Repeat("0", k)| == k
  decreases k
{
  if k > 0 { RepeatLen0(k - 1); }
}

lemma IntToStringHead(x: int)
  requires x != 0
  ensures |IntToString(x)| >= 1 && IntToString(x)[0] != '0'
  decreases if x < 0 then 1 - x else x
{
  if x < 0 {
    IntToStringHead(-x);
  } else if x >= 10 {
    IntToStringHead(x / 10);
  } else {
    assert x >= 1;
    assert DigitChar(x) != '0';
  }
}

lemma IterBound(cost: int, ln: nat, sl: nat, k: nat, dk: nat, jl: nat, v: int)
  requires ln >= 1
  requires dk >= 1
  requires k == 0 ==> sl == 0 && jl == 0 && ln == 1
  requires k >= 1 ==> jl == sl + k - 1 && sl >= ln
  requires cost <= 11 + 6 * ln + 7 * sl + k + dk
  ensures cost <= 26 * (dk + jl)
{
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= 27 * |output| + 2 * n + 1
{
  steps := 0;
  {
    var results: seq<string> := [];
    var t := 0;
    while t < n
      invariant 0 <= t <= n
      invariant |results| == 2 * t
      invariant steps <= 26 * SumLen(results)
      decreases n - t
    {
      ghost var s0 := steps;
      steps := steps + 2;
      steps := steps + 1;
      var v := a_list[t];
      steps := steps + Digits(v);
      var s := IntToString(v);
      IntToStringDigits(v);
      if v != 0 { IntToStringHead(v); }
      steps := steps + 1;
      var ln := |s|;
      var lst: seq<string> := [];
      var i := 0;
      ghost var s1 := steps;
      if v == 0 { assert s == "0"; }
      while i < ln
        invariant 0 <= i <= ln
        invariant v == 0 ==> |lst| == 0
        invariant steps <= s1 + 5 * i + 6 * SumLen(lst)
        invariant (i >= 1 && s[0] != '0') ==> SumLen(lst) >= ln
        decreases ln - i
      {
        RepeatLen0(ln - i - 1);
        SumLenSnoc(lst, [s[i]] + Repeat("0", ln - i - 1));
        steps := steps + 2;
        steps := steps + 2;
        if s[i] != '0' {
          steps := steps + (5 + |"0"| * (ln - i - 1) + |Repeat("0", ln - i - 1)| + |[[s[i]] + Repeat("0", ln - i - 1)]|);
          lst := lst + [[s[i]] + Repeat("0", ln - i - 1)];
        }
        steps := steps + 1;
        i := i + 1;
      }
      steps := steps + 1;
      steps := steps + (3 + Digits(|lst|) + (SumLen(lst) + |lst|) + |[IntToString(|lst|), Join(lst, " ")]|);
      IntToStringDigits(|lst|);
      ghost var dk := Digits(|lst|);
      ghost var jl := |Join(lst, " ")|;
      if |lst| >= 1 {
        JoinLen(lst, " ");
      } else {
        assert v == 0;
        assert ln == 1;
      }
      IterBound(steps - s0, ln, SumLen(lst), |lst|, dk, jl, v);
      SumLenSnoc(results, IntToString(|lst|));
      SumLenSnoc(results + [IntToString(|lst|)], Join(lst, " "));
      results := results + [IntToString(|lst|), Join(lst, " ")];
      assert results == (results[..|results| - 2] + [IntToString(|lst|)]) + [Join(lst, " ")];
      steps := steps + 1;
      t := t + 1;
    }
    steps := steps + 1;
    steps := steps + (SumLen(results) + |results|);
    if n >= 1 {
      JoinLen(results, "\n");
    }
    output := Join(results, "\n");
  }
}

import opened Prelude
