// 1352_A. Sum of Round Numbers  (problem 1263, solution 1263_2538)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../../prelude.dfy"

lemma RepLen(k: nat)
  ensures |Repeat("0", k)| == k
{
}

lemma DigitsLe(x: int)
  requires x >= 0
  ensures Digits(x) <= x + 1
  decreases x
{
  if x >= 10 { DigitsLe(x / 10); }
}

lemma SumDigitsSnoc(a: seq<int>, k: nat)
  requires k < |a|
  ensures SumDigits(a[..k + 1]) == SumDigits(a[..k]) + Digits(a[k])
  decreases k
{
  if k == 0 {
    assert a[..1] == [a[0]];
    assert a[..0] == [];
  } else {
    assert a[..k + 1][1..] == a[1..][..k];
    assert a[..k][1..] == a[1..][..k - 1];
    SumDigitsSnoc(a[1..], k - 1);
    assert a[1..][..k - 1 + 1] == a[1..][..k];
  }
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= 11 * n + 11 * SumDigits(a_list) + 4 * |output| + 4
{
  steps := 0;
  {
    var results: seq<string> := [];
    var t := 0;
    ghost var dsum := 0;
    while t < n
      invariant 0 <= t <= n
      invariant dsum == SumDigits(a_list[..t])
      invariant steps <= 11 * t + 11 * dsum + 3 * SumLen(results)
      decreases n - t
    {
      steps := steps + 2;
      steps := steps + 1;
      var v := a_list[t];
      steps := steps + Digits(v);
      var s := IntToString(v);
      IntToStringDigits(v);
      steps := steps + 1;
      var ln := |s|;
      var lst: seq<string> := [];
      var i := 0;
      ghost var b := steps;
      while i < ln
        invariant 0 <= i <= ln
        invariant |lst| <= i
        invariant steps <= b + 5 * i + 4 * |lst| + 2 * SumLen(lst)
        decreases ln - i
      {
        steps := steps + 2;
        steps := steps + 2;
        if s[i] != '0' {
          steps := steps + (5 + |"0"| * (ln - i - 1) + |Repeat("0", ln - i - 1)| + |[[s[i]] + Repeat("0", ln - i - 1)]|);
          RepLen(ln - i - 1);
          SumLenSnoc(lst, [s[i]] + Repeat("0", ln - i - 1));
          lst := lst + [[s[i]] + Repeat("0", ln - i - 1)];
        }
        steps := steps + 1;
        i := i + 1;
      }
      assert |lst| <= ln;
      ghost var c := IntToString(|lst|);
      IntToStringDigits(|lst|);
      DigitsLe(|lst|);
      ghost var j := Join(lst, " ");
      if |lst| >= 1 { JoinLen(lst, " "); }
      SumLenSnoc(results, c);
      SumLenSnoc(results + [c], j);
      assert results + [c, j] == (results + [c]) + [j];
      assert c == IntToString(|lst|) && j == Join(lst, " ");
      SumDigitsSnoc(a_list, t);
      dsum := dsum + ln;
      steps := steps + 1;
      steps := steps + (3 + Digits(|lst|) + (SumLen(lst) + |lst|) + |[IntToString(|lst|), Join(lst, " ")]|);
      results := results + [IntToString(|lst|), Join(lst, " ")];
      steps := steps + 1;
      t := t + 1;
    }
    steps := steps + 1;
    steps := steps + (SumLen(results) + |results|);
    assert a_list[..n] == a_list;
    output := Join(results, "\n");
    if |results| >= 1 { JoinLen(results, "\n"); }
  }
}

import opened Prelude
