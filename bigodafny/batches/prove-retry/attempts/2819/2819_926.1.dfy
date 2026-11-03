include "../../prelude.dfy"
import opened Prelude

method IntSqrtFloor(v: int) returns (r: int, ghost steps: nat)
  requires v >= 0
  ensures steps <= 8 * SearchPot(v + 1) + 6
{
  steps := 4;
  var lo := 0;
  var hi := v + 1;
  ghost var it: nat := 0;
  while lo < hi
    invariant 0 <= lo <= hi <= v + 1
    invariant it + SearchPot(hi - lo) <= SearchPot(v + 1)
    invariant steps == 4 + 8 * it
    decreases hi - lo
  {
    ghost var k := hi - lo;
    var mid := (lo + hi) / 2;
    if mid * mid <= v {
      lo := mid + 1;
    } else {
      hi := mid;
    }
    BisectStep(k, hi - lo);
    it := it + 1;
    steps := steps + 8;
  }
  r := lo - 1;
}

function RepStr(s: string, n: int): string
  decreases if n > 0 then n else 0
{
  if n <= 0 then "" else s + RepStr(s, n - 1)
}

ghost function TermOf(row: seq<int>): nat
{
  if |row| >= 2 then SearchPot((if 8 * row[1] - 7 < 0 then 0 else 8 * row[1] - 7) + 1) else 0
}

ghost function LogSum(pl: seq<seq<int>>, t: nat): nat
  requires t <= |pl|
  decreases t
{
  if t == 0 then 0 else LogSum(pl, t - 1) + TermOf(pl[t - 1])
}

lemma RepLenA(n: int)
  ensures |RepStr("a", n)| == (if n < 0 then 0 else n)
  decreases if n > 0 then n else 0
{
  if n > 0 { RepLenA(n - 1); }
}

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  ensures steps <= 40 * |pairs_list| + 10 * LogSum(pairs_list, |pairs_list|) + 3 * |output| + 12
  requires forall t :: 0 <= t < |pairs_list| && |pairs_list[t]| >= 2 ==>
    pairs_list[t][0] >= 3 && 1 <= pairs_list[t][1] &&
    2 * pairs_list[t][1] <= pairs_list[t][0] * (pairs_list[t][0] - 1)
{
  steps := 2;
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
    invariant |results| <= t
    invariant steps <= 2 + 40 * t + 10 * LogSum(pairs_list, t) + 2 * SumLen(results)
    decreases |pairs_list| - t
  {
    var row := pairs_list[t];
    if |row| >= 2 {
      var nn := row[0];
      var k := row[1];
      var val := 8 * k - 7;
      if val < 0 { val := 0; }
      var s, ss := IntSqrtFloor(val);
      steps := steps + ss;
      var x := FloorDiv(1 + s, 2);
      var d := FloorDiv(s - 1, 2);
      var b := FloorDiv(d * (d + 1), 2) + 1;
      var y := k - b;
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      RepLenA(nn - x - 1);
      RepLenA(x - y - 1);
      RepLenA(y);
      steps := steps + 2 * |r| + 30;
      SumLenSnoc(results, r);
      results := results + [r];
    }
    t := t + 1;
  }
  output := Join(results, "\n");
  if |results| >= 1 { JoinLen(results, "\n"); }
  steps := steps + SumLen(results) + |results|;
}
