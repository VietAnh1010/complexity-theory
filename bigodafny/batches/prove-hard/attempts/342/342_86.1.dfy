// --- Python ---------------------------------------------------------
// input()
// a = list(map(int , input().split()))
// m = min(a)
// print(sum(a)-max(i+m-i//j-m*j for i in set(a)
// for j in range(1 , int(i**.5) + 1)if i%j==0))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma JLe(j: int, v: int)
  requires j >= 1 && j * j <= v
  ensures j <= v
{
  assert j * j >= j * 1;
}

ghost function Pos(x: int): nat { if x > 0 then x else 0 }

ghost function SP(s: seq<int>, k: nat): nat
  requires k <= |s|
{
  if k == 0 then 0 else SP(s, k - 1) + Pos(s[k - 1])
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 20 * |a_list| + 12 * SP(a_list, |a_list|) + 8 + |output|
{
  steps := 0;
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps == 6 * idx
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
    invariant 0 <= idx <= |a_list|
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
    invariant 0 <= idx <= |a_list|
    invariant steps <= 13 * |a_list| + 5 + 7 * idx + 12 * SP(a_list, idx)
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 1;
    var v := a_list[idx];
    var j := 1;
    ghost var s0 := steps;
    while j * j <= v
      invariant 1 <= j <= Pos(v) + 1
      invariant steps <= s0 + 12 * (j - 1)
      decreases v - j * j
    {
      JLe(j, v);
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
    idx := idx + 1;
    assert SP(a_list, idx) == SP(a_list, idx - 1) + Pos(a_list[idx - 1]);
  }
  steps := steps + 2;
  steps := steps + (1 + Digits(total - diff));
  output := IntToString(total - diff);
  IntToStringDigits(total - diff);
}

import opened Prelude
