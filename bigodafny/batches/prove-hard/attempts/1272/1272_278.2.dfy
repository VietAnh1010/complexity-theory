// --- Python ---------------------------------------------------------
// def solve(arr):
//     for i in range(0,len(arr)-1):
//         x = arr[i+1].find(arr[i])
//        # print(x)
//         if x == -1:
//             return 0
//     return 1
// n=int(input())
// arr = []
// while n:
//     s = str(input())
//     arr.append(s)
//     n=n-1
// arr.sort(key=len)
// flag = solve(arr)
// if flag:
//     print("YES")
//     for i in arr:
//         print(i)
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

function ContainsFrom1272b(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then
    false
  else if hay[pos .. pos + |needle|] == needle then
    true
  else
    ContainsFrom1272b(hay, needle, pos + 1)
}

ghost function ContainsFrom1272b_steps(hay: string, needle: string, pos: nat): nat
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  5 + if pos + |needle| > |hay| then 0 else 5 + if hay[pos .. pos + |needle|] == needle then 0 else 1 + ContainsFrom1272b_steps(hay, needle, pos + 1)
}

function Contains1272b(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272b(hay, needle, 0)
}

ghost function Contains1272b_steps(hay: string, needle: string): nat
{
  3 + if |needle| == 0 then 0 else ContainsFrom1272b_steps(hay, needle, 0)
}

lemma SumLenCons(x: string, rest: seq<string>)
  ensures SumLen([x] + rest) == |x| + SumLen(rest)
{
  assert ([x] + rest)[1..] == rest;
}

lemma SumLenMerge(a: seq<string>, b: seq<string>, less: (string, string) -> bool)
  ensures SumLen(Merge(a, b, less)) == SumLen(a) + SumLen(b)
  decreases |a| + |b|
{
  if |a| == 0 {
    assert SumLen(a) == 0;
  } else if |b| == 0 {
    assert SumLen(b) == 0;
  } else if less(b[0], a[0]) {
    SumLenMerge(a, b[1..], less);
    SumLenCons(b[0], Merge(a, b[1..], less));
    assert b == [b[0]] + b[1..];
    SumLenCons(b[0], b[1..]);
  } else {
    SumLenMerge(a[1..], b, less);
    SumLenCons(a[0], Merge(a[1..], b, less));
    assert a == [a[0]] + a[1..];
    SumLenCons(a[0], a[1..]);
  }
}

lemma SumLenSplit(a: seq<string>, b: seq<string>)
  ensures SumLen(a + b) == SumLen(a) + SumLen(b)
  decreases |a|
{
  if |a| > 0 {
    assert (a + b)[1..] == a[1..] + b;
    SumLenSplit(a[1..], b);
  } else {
    assert a + b == b;
  }
}

lemma SumLenSort(s: seq<string>, less: (string, string) -> bool)
  ensures SumLen(Sort(s, less)) == SumLen(s)
  decreases |s|
{
  if |s| > 1 {
    var k := |s| / 2;
    SumLenSort(s[..k], less);
    SumLenSort(s[k..], less);
    SumLenMerge(Sort(s[..k], less), Sort(s[k..], less), less);
    assert s == s[..k] + s[k..];
    SumLenSplit(s[..k], s[k..]);
  }
}

lemma SortByLen(s: seq<string>)
  ensures SumLen(Sort(s, (x: string, y: string) => |x| < |y|)) == SumLen(s)
{
  SumLenSort(s, (x: string, y: string) => |x| < |y|);
}

lemma ContainsBound(hay: string, needle: string, pos: nat)
  requires 1 <= |needle|
  requires pos <= |hay|
  ensures ContainsFrom1272b_steps(hay, needle, pos) <= 11 * (|hay| - pos) + 5
  decreases |hay| - pos
{
  if pos + |needle| <= |hay| && hay[pos .. pos + |needle|] != needle {
    ContainsBound(hay, needle, pos + 1);
  }
}

lemma ContainsTotal(hay: string, needle: string)
  ensures Contains1272b_steps(hay, needle) <= 11 * |hay| + 8
{
  if |needle| >= 1 { ContainsBound(hay, needle, 0); }
}

ghost function PartSum(arr: seq<string>, i: nat): nat
{
  if i + 1 <= |arr| then SumLen(arr[..i + 1]) else 0
}

lemma PartSumStep(arr: seq<string>, i: nat)
  requires i + 1 < |arr|
  ensures PartSum(arr, i + 1) == PartSum(arr, i) + |arr[i + 1]|
{
  assert arr[..i + 2] == arr[..i + 1] + [arr[i + 1]];
  SumLenSnoc(arr[..i + 1], arr[i + 1]);
}

lemma PartSumLe(arr: seq<string>, i: nat)
  ensures PartSum(arr, i) <= SumLen(arr)
{
  if i + 1 <= |arr| { SumLenPrefix(arr, i + 1); }
}

lemma SumLenStep(arr: seq<string>, m: nat)
  requires m < |arr|
  ensures SumLen(arr[..m + 1]) == SumLen(arr[..m]) + |arr[m]|
{
  assert arr[..m + 1] == arr[..m] + [arr[m]];
  SumLenSnoc(arr[..m], arr[m]);
}

method Solve(n: int, strings: seq<string>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|strings|) + 40 * |strings| + 30 * SumLen(strings) + 40
{
  steps := 0;
  steps := steps + SortCost(|strings|);
  var arr := Sort(strings, (x: string, y: string) => |x| < |y|);
  SortByLen(strings);
  SortCostWithin(|strings|, |strings|);
  LinearLeNLogN(|strings|);
  var flag := true;
  var i := 0;
  while i < |arr| - 1
    invariant 0 <= i && (i <= |arr| - 1 || (|arr| == 0 && i == 0))
    invariant steps <= SortCost(|strings|) + 17 * i + 11 * PartSum(arr, i)
    decreases |arr| - 1 - i
  {
    ContainsTotal(arr[i + 1], arr[i]);
    PartSumStep(arr, i);
    steps := steps + 4;
    steps := steps + (4 + Contains1272b_steps(arr[i + 1], arr[i]));
    if !Contains1272b(arr[i + 1], arr[i]) {
      flag := false;
    }
    steps := steps + 1;
    i := i + 1;
  }
  PartSumLe(arr, i);
  steps := steps + 3;
  if flag {
    steps := steps + 1;
    var lines: seq<string> := ["YES"];
    var m := 0;
    assert arr[..0] == [];
    assert ["YES"] + [] == ["YES"];
    SumLenCons("YES", []);
    assert SumLen(lines) == 3 + SumLen(arr[..m]);
    while m < |arr|
      invariant 0 <= m <= |arr|
      invariant |lines| == 1 + m
      invariant SumLen(lines) == 3 + SumLen(arr[..m])
      invariant steps <= SortCost(|strings|) + 17 * |arr| + 11 * SumLen(arr) + 4 + 7 * m
      decreases |arr| - m
    {
      SumLenSnoc(lines, arr[m]);
      SumLenStep(arr, m);
      steps := steps + 3;
      steps := steps + (2 + |[arr[m]]|);
      lines := lines + [arr[m]];
      steps := steps + 1;
      m := m + 1;
    }
    steps := steps + 2;
    steps := steps + (SumLen(lines) + |lines|);
    output := Join(lines, "\n");
  } else {
    output := "NO";
  }
}

import opened Prelude
