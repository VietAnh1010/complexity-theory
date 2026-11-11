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
  ensures steps <= 20 * |a_list| + 12 * SumPos(a_list, |a_list|) + 9 + |output|
{
  steps := 0;
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
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
  ghost var base := steps;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant base <= 13 * |a_list| + 6
    invariant steps <= base + 7 * idx + 12 * SumPos(a_list, idx)
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 1;
    var v := a_list[idx];
    var j := 1;
    ghost var s0 := steps;
    while j * j <= v
      invariant 1 <= j <= ISqrt(v) + 1
      invariant steps <= s0 + 12 * (j - 1)
      decreases v - j * j
    {
      JLe(j, v);
      assert j <= ISqrt(v);
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
  }
  steps := steps + 2;
  IntToStringDigits(total - diff);
  steps := steps + (1 + Digits(total - diff));
  output := IntToString(total - diff);
}

import opened Prelude

ghost function Pos(v: int): nat { if v > 0 then v else 0 }

ghost function SumPos(a: seq<int>, k: nat): nat
  requires k <= |a|
{
  if k == 0 then 0 else SumPos(a, k - 1) + ISqrt(a[k - 1])
}

ghost function Sq(v: int, k: nat): nat
  requires k * k <= v
  decreases v - k
{
  if (k + 1) * (k + 1) > v then k
  else
    (assert k + 1 <= (k + 1) * (k + 1);
     Sq(v, k + 1))
}

lemma SqProp(v: int, k: nat)
  requires k * k <= v
  ensures Sq(v, k) * Sq(v, k) <= v && v < (Sq(v, k) + 1) * (Sq(v, k) + 1)
  decreases v - k
{
  if (k + 1) * (k + 1) <= v {
    assert k + 1 <= (k + 1) * (k + 1);
    SqProp(v, k + 1);
  }
}

ghost function ISqrt(v: int): nat
{
  if v <= 0 then 0 else Sq(v, 0)
}

lemma JLe(j: int, v: int)
  requires 1 <= j && j * j <= v
  ensures j <= ISqrt(v)
{
  SqProp(v, 0);
  var r := Sq(v, 0);
  if j > r {
    assert (r + 1) * (r + 1) <= j * j;
  }
}
