include "../../../../prelude.dfy"
method IntSqrtFloor(v: int) returns (r: int, ghost steps: nat)
  requires v >= 0
  ensures steps <= 7 * SearchPot(v + 1) + 3
{
  steps := 0;
  var lo := 0;
  steps := steps + 1;
  var hi := v + 1;
  ghost var it: nat := 0;
  while lo < hi
    invariant 0 <= lo <= hi <= v + 1
    invariant it + SearchPot(hi - lo) <= SearchPot(v + 1)
    invariant steps <= 1 + 7 * it
    decreases hi - lo
  {
    ghost var k := hi - lo;
    steps := steps + 2;
    steps := steps + 2;
    var mid := (lo + hi) / 2;
    steps := steps + 2;
    if mid * mid <= v {
      steps := steps + 1;
      lo := mid + 1;
    } else {
      hi := mid;
    }
    BisectStep(k, hi - lo);
    it := it + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  r := lo - 1;
}

function RepStr(s: string, n: int): string
  decreases if n > 0 then n else 0
{
  if n <= 0 then
    ""
  else
    s + RepStr(s, n - 1)
}

ghost function RepStr_steps(s: string, n: int): nat
  decreases if n > 0 then n else 0
{
  2 + if n <= 0 then 0 else 1 + RepStr_steps(s, n - 1) + |RepStr(s, n - 1)|
}

ghost function PieceSteps(row: seq<int>): nat
{
  if |row| >= 2 then SearchPot((if 8 * row[1] - 7 < 0 then 0 else 8 * row[1] - 7) + 1) else 0
}

ghost function LogSum(pl: seq<seq<int>>, t: nat): nat
  requires t <= |pl|
  decreases t
{
  if t == 0 then 0 else LogSum(pl, t - 1) + PieceSteps(pl[t - 1])
}

ghost function SqSum(rs: seq<string>): nat
  decreases |rs|
{
  if |rs| == 0 then 0 else SqSum(rs[..|rs| - 1]) + |rs[|rs| - 1]| * |rs[|rs| - 1]|
}

lemma SqSumSnoc(rs: seq<string>, r: string)
  ensures SqSum(rs + [r]) == SqSum(rs) + |r| * |r|
{
  assert (rs + [r])[..|rs|] == rs;
}

lemma SqAdd2819(s: nat, a: nat, b: nat)
  requires s <= a * a
  ensures s + b * b <= (a + b) * (a + b)
{
  assert (a + b) * (a + b) == a * a + 2 * (a * b) + b * b;
  assert a * b >= 0;
}

lemma SqSumLe(rs: seq<string>)
  ensures SqSum(rs) <= SumLen(rs) * SumLen(rs)
  decreases |rs|
{
  if |rs| > 0 {
    var h := rs[..|rs| - 1];
    var l := rs[|rs| - 1];
    SqSumLe(h);
    assert rs == h + [l];
    SumLenSnoc(h, l);
    SqSumSnoc(h, l);
    SqAdd2819(SqSum(h), SumLen(h), |l|);
  }
}

lemma RepLenA(n: int)
  ensures |RepStr("a", n)| == (if n < 0 then 0 else n)
  decreases if n > 0 then n else 0
{
  if n > 0 { RepLenA(n - 1); }
}

lemma RepStepsBound(n: int)
  ensures RepStr_steps("a", n) <= |RepStr("a", n)| * |RepStr("a", n)| + 3 * |RepStr("a", n)| + 2
  decreases if n > 0 then n else 0
{
  RepLenA(n);
  if n > 0 {
    RepLenA(n - 1);
    RepStepsBound(n - 1);
    var m := n - 1;
    assert (m + 1) * (m + 1) == m * m + 2 * m + 1;
  }
}

lemma PieceSq(m1: nat, m2: nat, m3: nat, L: nat)
  requires m1 + m2 + m3 <= L
  ensures m1 * m1 + m2 * m2 + m3 * m3 <= L * L
{
  CostMulMono(m1, m1, L);
  CostMulMono(m2, m2, L);
  CostMulMono(m3, m3, L);
  CostMulDistrib(m1, m2 + m3, m1 + m2 + m3, L);
  CostMulDistrib(m2, m3, m2 + m3, L);
  CostMulMonoLeft(m1 + m2 + m3, L, L);
}

method Solve(n: int, pairs_list: seq<seq<int>>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 70 * |pairs_list| + 10 * LogSum(pairs_list, |pairs_list|) + 9 * |output| + 2 * (|output| * |output|) + 12
  requires forall t :: 0 <= t < |pairs_list| && |pairs_list[t]| >= 2 ==> pairs_list[t][0] >= 3 && 1 <= pairs_list[t][1] && 2 * pairs_list[t][1] <= pairs_list[t][0] * (pairs_list[t][0] - 1)
{
  steps := 0;
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
    invariant |results| <= t
    invariant steps <= 70 * t + 10 * LogSum(pairs_list, t) + 8 * SumLen(results) + 2 * SqSum(results)
    decreases |pairs_list| - t
  {
    steps := steps + 3;
    steps := steps + 1;
    var row := pairs_list[t];
    steps := steps + 2;
    if |row| >= 2 {
      steps := steps + 1;
      var nn := row[0];
      steps := steps + 1;
      var k := row[1];
      steps := steps + 2;
      var val := 8 * k - 7;
      steps := steps + 1;
      if val < 0 {
        val := 0;
      }
      var s, s0 := IntSqrtFloor(val);
      steps := steps + s0;
      steps := steps + (1 + 1);
      var x := FloorDiv(1 + s, 2);
      steps := steps + (1 + 1);
      var d := FloorDiv(s - 1, 2);
      steps := steps + (3 + 1);
      var b := FloorDiv(d * (d + 1), 2) + 1;
      steps := steps + 1;
      var y := k - b;
      steps := steps + (4 + RepStr_steps("a", nn - x - 1) + |"b"| + RepStr_steps("a", x - y - 1) + |RepStr("a", x - y - 1)| + |"b"| + RepStr_steps("a", y) + |RepStr("a", y)|);
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      RepLenA(nn - x - 1);
      RepLenA(x - y - 1);
      RepLenA(y);
      RepStepsBound(nn - x - 1);
      RepStepsBound(x - y - 1);
      RepStepsBound(y);
      PieceSq(|RepStr("a", nn - x - 1)|, |RepStr("a", x - y - 1)|, |RepStr("a", y)|, |r|);
      SumLenSnoc(results, r);
      SqSumSnoc(results, r);
      steps := steps + (1 + |[r]|);
      results := results + [r];
    }
    steps := steps + 1;
    t := t + 1;
  }
  steps := steps + 2;
  steps := steps + (SumLen(results) + |results|);
  output := Join(results, "\n");
  SqSumLe(results);
  if |results| >= 1 { JoinLen(results, "\n"); }
  CostMulMonoLeft(SumLen(results), |output|, SumLen(results));
  CostMulMono(|output|, SumLen(results), |output|);
}

import opened Prelude
