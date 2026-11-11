// --- Python ---------------------------------------------------------
// n = int(input())
//
// a = list(map(int, input().split()))
//
// p = a[0]
// a = [(p, 0)] + sorted([(a[i], i) for i in range(1, n)], reverse=True)
//
// result = ""
//
// got = {0}
//
// for i in range(n):
// 	temp_a = a[i][0]
// 	temp_i = i + 1
//
// 	while temp_a > 0 and temp_i < n:
// 		if temp_i not in got:
// 			got.add(temp_i)
// 			temp_a -= 1
// 			result += str(a[i][1] + 1) + " " + str(a[temp_i][1] + 1) + "\n"
//
// 		temp_i += 1
//
// if len(got) < n:
// 	print(-1)
// else:
// 	print(n - 1)
// 	print(result)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function Cnt(s: seq<bool>): nat
  decreases |s|
{
  if |s| == 0 then 0 else Cnt(s[..|s| - 1]) + (if s[|s| - 1] then 1 else 0)
}

lemma CntLe(s: seq<bool>)
  ensures Cnt(s) <= |s|
  decreases |s|
{
  if |s| > 0 { CntLe(s[..|s| - 1]); }
}

lemma CntSet(s: seq<bool>, t: nat)
  requires t < |s|
  requires !s[t]
  ensures Cnt(s[t := true]) == Cnt(s) + 1
  decreases |s|
{
  var u := s[t := true];
  if t == |s| - 1 {
    assert u[..|u| - 1] == s[..|s| - 1];
  } else {
    assert u[..|u| - 1] == s[..|s| - 1][t := true];
    CntSet(s[..|s| - 1], t);
  }
}

lemma DigitsLe(x: int)
  requires x >= 0
  ensures Digits(x) <= x + 1
  decreases x
{
  if x >= 10 { DigitsLe(x / 10); }
}

lemma FinalArith(n: nat)
  ensures n * (7 * n + 9) + n * (4 * n + 30) <= 11 * (n * n) + 39 * n
{
  assert n * (7 * n + 9) == 7 * (n * n) + 9 * n;
  assert n * (4 * n + 30) == 4 * (n * n) + 30 * n;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + 11 * (n * n) + 50 * n + 2 * |output| + 40
{
  steps := 0;
  var pairs: seq<(int, int)> := [];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |pairs| == i - 1
    invariant steps <= 7 * (i - 1)
    invariant forall x :: x in pairs ==> 1 <= x.1 < n
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + (3 + |[(a_list[i], i)]|);
    pairs := pairs + [(a_list[i], i)];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + SortCost(|pairs|);
  SortCostWithin(|pairs|, n);
  var sorted := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  SortKeepsElems(pairs, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  steps := steps + (3 + |sorted|);
  var a := [(a_list[0], 0)] + sorted;
  steps := steps + n;
  var got := seq(n, _ /* _v0 */ => false);
  var gotCount := 0;
  steps := steps + 1;
  if n > 0 {
    steps := steps + 1;
    got := got[0 := true];
    gotCount := 1;
  }
  assert forall k :: 0 <= k < n ==> 0 <= a[k].1 < n by {
    forall k | 0 <= k < n ensures 0 <= a[k].1 < n {
      if k > 0 { assert a[k] == sorted[k - 1]; assert sorted[k - 1] in sorted; }
    }
  }
  ghost var S0 := steps;
  assert S0 <= 2 * NLogN(n) + 9 * n + 10;
  ghost var base := Cnt(got);
  ghost var sc: nat := 0;
  ghost var m := 7 * n + 9;
  ghost var kc := 4 * n + 30;
  var lines: seq<string> := [];
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant |got| == n
    invariant |a| == n
    invariant forall k :: 0 <= k < n ==> 0 <= a[k].1 < n
    invariant m == 7 * n + 9 && kc == 4 * n + 30
    invariant Cnt(got) == base + sc
    invariant steps <= S0 + idx * m + sc * kc
  {
    steps := steps + 2;
    steps := steps + 2;
    var temp_a := a[idx].0;
    steps := steps + 1;
    var temp_i := idx + 1;
    while temp_a > 0 && temp_i < n
      invariant idx + 1 <= temp_i <= n
      invariant |got| == n
      invariant Cnt(got) == base + sc
      invariant steps <= S0 + idx * m + sc * kc + 5 + 7 * (temp_i - idx - 1)
      decreases n - temp_i
    {
      steps := steps + (3 + if temp_a > 0 then 1 else 0);
      steps := steps + 2;
      if !got[temp_i] {
        CntSet(got, temp_i);
        CntLe(got[temp_i := true]);
        IntToStringDigits(a[temp_i].1 + 1);
        IntToStringDigits(a[idx].1 + 1);
        DigitsLe(a[temp_i].1 + 1);
        DigitsLe(a[idx].1 + 1);
        CostMulDistrib(sc, 1, sc + 1, kc);
        sc := sc + 1;
        steps := steps + 1;
        got := got[temp_i := true];
        steps := steps + 1;
        gotCount := gotCount + 1;
        steps := steps + 1;
        temp_a := temp_a - 1;
        steps := steps + (7 + Digits(a[idx].1 + 1) + |" "| + Digits(a[temp_i].1 + 1) + |IntToString(a[temp_i].1 + 1)| + |[IntToString(a[idx].1 + 1) + " " + IntToString(a[temp_i].1 + 1)]|);
        lines := lines + [IntToString(a[idx].1 + 1) + " " + IntToString(a[temp_i].1 + 1)];
      }
      steps := steps + 1;
      temp_i := temp_i + 1;
    }
    steps := steps + (2 + if temp_a > 0 then 1 else 0);
    steps := steps + 1;
    CntLe(got);
    CostMulDistrib(idx, 1, idx + 1, m);
    idx := idx + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  CntLe(got);
  FinalArith(n);
  CostMulMonoLeft(sc, n, kc);
  assert idx * m == n * m;
  if gotCount < n {
    output := "-1\n";
  } else {
    if |lines| > 0 { JoinLen(lines, "\n"); }
    steps := steps + (3 + if |lines| > 0 then SumLen(lines) + |lines| + |"\n"| else 0);
    var rawResult := if |lines| > 0 then Join(lines, "\n") + "\n" else "";
    IntToStringDigits(n - 1);
    DigitsLe(n - 1);
    steps := steps + (1 + Digits(n - 1) + |"\n"| + |rawResult| + |"\n"|);
    output := IntToString(n - 1) + "\n" + rawResult + "\n";
  }
}

import opened Prelude
