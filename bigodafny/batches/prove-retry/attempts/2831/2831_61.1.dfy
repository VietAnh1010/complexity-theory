// 769_B. News About Credit  (problem 2831, solution 2831_61)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

ghost function Cnt2831(s: seq<bool>): nat
  decreases |s|
{
  if |s| == 0 then 0 else Cnt2831(s[..|s| - 1]) + (if s[|s| - 1] then 1 else 0)
}

lemma CntLe2831(s: seq<bool>)
  ensures Cnt2831(s) <= |s|
  decreases |s|
{
  if |s| > 0 { CntLe2831(s[..|s| - 1]); }
}

lemma CntFalse2831(n: nat)
  ensures Cnt2831(seq(n, _ => false)) == 0
  decreases n
{
  if n > 0 {
    assert seq(n, _ => false)[..n - 1] == seq(n - 1, _ => false);
    CntFalse2831(n - 1);
  }
}

lemma CntSet2831(s: seq<bool>, i: nat)
  requires i < |s| && !s[i]
  ensures Cnt2831(s[i := true]) == Cnt2831(s) + 1
  decreases |s|
{
  var t := s[i := true];
  if i == |s| - 1 {
    assert t[..|s| - 1] == s[..|s| - 1];
  } else {
    assert t[..|t| - 1] == s[..|s| - 1][i := true];
    CntSet2831(s[..|s| - 1], i);
  }
}

lemma DigitsLe2831(x: int)
  requires x >= 0
  ensures Digits(x) <= x + 1
  decreases x
{
  if x >= 10 { DigitsLe2831(x / 10); }
}

lemma Lin2831(n: nat, a: nat, b: nat)
  ensures n * (a * n + b) == a * (n * n) + b * n
{
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + 11 * (n * n) + 50 * n + 50 + 4 * |output|
{
  steps := 1;
  var pairs: seq<(int,int)> := [];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |pairs| == i - 1
    invariant forall k :: 0 <= k < |pairs| ==> 0 <= pairs[k].1 < n
    invariant steps == 1 + 5 * (i - 1)
    decreases n - i
  {
    pairs := pairs + [(a_list[i], i)];
    i := i + 1;
    steps := steps + 5;
  }
  var less := (x: (int,int), y: (int,int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1);
  var sorted := Sort(pairs, less);
  SortKeepsElems(pairs, less);
  steps := steps + SortCost(|pairs|);
  SortCostWithin(|pairs|, n);
  var a := [(a_list[0], 0)] + sorted;
  steps := steps + |sorted| + 2;
  var got := seq(n, _ => false);
  steps := steps + n;
  CntFalse2831(n);
  var gotCount := 0;
  if n > 0 {
    got := got[0 := true];
    gotCount := 1;
    CntSet2831(seq(n, _ => false), 0);
    steps := steps + 3;
  }
  ghost var M: nat := 3 * n + 20;
  ghost var K2: nat := 8 * n + 10;
  ghost var B: nat := steps;
  var lines: seq<string> := [];
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant |got| == n
    invariant |a| == n
    invariant forall k :: 0 <= k < n ==> 0 <= a[k].1 < n
    invariant steps <= B + idx * K2 + Cnt2831(got) * M
    invariant Cnt2831(got) <= n
    decreases n - idx
  {
    var temp_a := a[idx].0;
    var temp_i := idx + 1;
    CntLe2831(got);
    while temp_a > 0 && temp_i < n
      invariant idx + 1 <= temp_i <= n
      invariant |got| == n
      invariant steps <= B + idx * K2 + 8 * (temp_i - idx - 1) + Cnt2831(got) * M
      invariant Cnt2831(got) <= n
      decreases n - temp_i
    {
      if !got[temp_i] {
        CntSet2831(got, temp_i);
        CostMulDistrib(Cnt2831(got), 1, Cnt2831(got) + 1, M);
        DigitsLe2831(a[idx].1 + 1);
        DigitsLe2831(a[temp_i].1 + 1);
        got := got[temp_i := true];
        gotCount := gotCount + 1;
        temp_a := temp_a - 1;
        lines := lines + [IntToString(a[idx].1 + 1) + " " + IntToString(a[temp_i].1 + 1)];
        CntLe2831(got);
        steps := steps + M;
      }
      temp_i := temp_i + 1;
      steps := steps + 8;
    }
    CostMulDistrib(idx, 1, idx + 1, K2);
    idx := idx + 1;
    steps := steps + 2;
  }
  CostMulMonoLeft(Cnt2831(got), n, M);
  Lin2831(n, 8, 10);
  Lin2831(n, 3, 20);
  assert n * K2 == 8 * (n * n) + 10 * n;
  assert n * M == 3 * (n * n) + 20 * n;
  if gotCount < n {
    output := "-1\n";
    steps := steps + 2;
  } else {
    JoinLen(lines, "\n");
    var rawResult := if |lines| > 0 then Join(lines, "\n") + "\n" else "";
    IntToStringDigits(n - 1);
    output := IntToString(n - 1) + "\n" + rawResult + "\n";
    steps := steps + SumLen(lines) + |lines| + 1 + Digits(n - 1) + 1 + |rawResult| + 1 + 4;
  }
}
