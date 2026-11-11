// --- Python ---------------------------------------------------------
// input()
// a = list(map(int , input().split()))
// m = min(a)
// print(sum(a)-max(i+m-i//j-m*j for i in set(a)
// for j in range(1 , int(i**.5) + 1)if i%j==0))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 20 * |a_list| + 12 * SumPos(a_list) + 10 + |output|
{
  steps := 0;
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    invariant idx <= |a_list|
    invariant steps <= 6 * idx
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 2;
    total := total + a_list[idx];
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  steps := steps + 1;
  var m := a_list[0];
  idx := 0;
  while idx < |a_list|
    invariant idx <= |a_list|
    invariant steps <= 6 * |a_list| + 3 + 7 * idx
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 2;
    if a_list[idx] < m {
      steps := steps + 1;
      m := a_list[idx];
    }
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  var diff := 0;
  idx := 0;
  while idx < |a_list|
    invariant idx <= |a_list|
    invariant steps <= 13 * |a_list| + 5 + 7 * idx + 12 * SumPos(a_list[..idx])
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 1;
    var v := a_list[idx];
    var j := 1;
    ghost var s0 := steps;
    while j * j <= v
      invariant j >= 1
      invariant j - 1 + RootAux(v, j) == Pos(v)
      invariant steps <= s0 + 12 * (j - 1)
      decreases v - j * j
    {
      JLe(v, j);
      steps := steps + 3;
      steps := steps + 2;
      if v % j == 0 {
        steps := steps + 5;
        var term := v + m - v / j - m * j;
        steps := steps + 1;
        if term > diff {
          diff := term;
        }
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    SumPosStep(a_list, idx);
    idx := idx + 1;
  }
  assert a_list[..idx] == a_list;
  steps := steps + 2;
  steps := steps + (1 + Digits(total - diff));
  output := IntToString(total - diff);
  IntToStringDigits(total - diff);
}

import opened Prelude

ghost function RootAux(v: int, j: int): nat
  requires j >= 1
  decreases if j * j <= v then v - j * j + 1 else 0
{
  if j * j <= v then 1 + RootAux(v, j + 1) else 0
}

ghost function Pos(v: int): nat { RootAux(v, 1) }

ghost function SumPos(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0 else SumPos(s[..|s|-1]) + Pos(s[|s|-1])
}

lemma JLe(v: int, j: int)
  requires j >= 1
  requires j * j <= v
  ensures RootAux(v, j) == 1 + RootAux(v, j + 1)
{
}

lemma SumPosStep(a: seq<int>, i: nat)
  requires i < |a|
  ensures SumPos(a[..i+1]) == SumPos(a[..i]) + Pos(a[i])
{
  assert a[..i+1][..i] == a[..i];
}
