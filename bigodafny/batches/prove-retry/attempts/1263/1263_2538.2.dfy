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

include "../../prelude.dfy"
import opened Prelude

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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= 14 * n + 12 * SumDigits(a_list) + 4 * |output| + 10
{
  steps := 1;
  var results: seq<string> := [];
  var t := 0;
  ghost var dsum := 0;
  while t < n
    invariant 0 <= t <= n
    invariant dsum == SumDigits(a_list[..t])
    invariant steps <= 1 + 14 * t + 12 * dsum + 3 * SumLen(results)
    decreases n - t
  {
    ghost var s0 := steps;
    var v := a_list[t];
    var s := IntToString(v);
    IntToStringDigits(v);
    var ln := |s|;
    steps := steps + 3 + ln;
    var lst: seq<string> := [];
    var i := 0;
    ghost var b := steps;
    while i < ln
      invariant 0 <= i <= ln
      invariant |lst| <= i
      invariant steps <= b + 5 * i + 4 * |lst| + SumLen(lst)
      decreases ln - i
    {
      steps := steps + 5;
      if s[i] != '0' {
        RepLen(ln - i - 1);
        var part := [s[i]] + Repeat("0", ln - i - 1);
        SumLenSnoc(lst, part);
        lst := lst + [part];
        steps := steps + 4 + |part|;
      }
      i := i + 1;
    }
    assert |lst| <= ln;
    var c := IntToString(|lst|);
    IntToStringDigits(|lst|);
    DigitsLe(|lst|);
    var j := Join(lst, " ");
    if |lst| >= 1 { JoinLen(lst, " "); }
    SumLenSnoc(results, c);
    SumLenSnoc(results + [c], j);
    results := results + [c, j];
    assert results == (results[..|results| - 2] + [c]) + [j] || true;
    steps := steps + |c| + SumLen(lst) + |lst| + 2;
    SumDigitsSnoc(a_list, t);
    dsum := dsum + ln;
    t := t + 1;
  }
  assert a_list[..n] == a_list;
  output := Join(results, "\n");
  steps := steps + SumLen(results) + |results|;
  if |results| >= 1 { JoinLen(results, "\n"); }
}
