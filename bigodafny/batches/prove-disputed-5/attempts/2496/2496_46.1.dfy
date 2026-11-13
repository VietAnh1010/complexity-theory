include "../../prelude.dfy"
import opened Prelude

ghost function C1f(m: nat): nat { 8 * m + 12 }
ghost function C2f(m: nat): nat { m * C1f(m) + 12 }
ghost function Cub(m: nat): nat { m * C2f(m) }

method Solve(n: int, a_list: seq<real>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 2 * NLogN(|a_list|) + 6 * |a_list| + Cub(|a_list|) + 400 + 2 * |output|
{
  ghost var M := |a_list|;
  steps := 1 + SortCost(M);
  SortCostNLogN(M);
  var ls := Sort(a_list, (x: real, y: real) => x < y);
  var m := |ls|;
  var mx := ls[m - 1];
  var idx := 0;
  while idx < m && ls[idx] < 0.5
    invariant 0 <= idx <= m
    invariant m == M
    invariant steps <= 1 + SortCost(M) + 6 * idx
  {
    idx := idx + 1;
    steps := steps + 6;
  }
  steps := steps + 4;
  if idx < m && ls[idx] < 0.5 {
    idx := idx + 1;
  }

  var res: real := 0.0;
  var st := 0;
  ghost var C1 := C1f(M);
  ghost var C2 := C2f(M);
  ghost var s00 := steps;
  while st < idx - 1
    invariant 0 <= st <= (if idx > 1 then idx - 1 else 0)
    invariant idx <= m == M
    invariant steps <= s00 + st * C2
  {
    ghost var s0 := steps;
    var temp: real := 0.0;
    var i := st;
    while i < idx
      invariant st <= i <= idx
      invariant steps <= s0 + (i - st) * C1
    {
      var t: real := 1.0;
      var j := st;
      ghost var s1 := steps;
      while j < idx
        invariant st <= j <= idx
        invariant steps <= s1 + 8 * (j - st)
      {
        steps := steps + 8;
        if i != j {
          t := t * (1.0 - ls[j]);
        }
        j := j + 1;
      }
      temp := temp + t * ls[i];
      steps := steps + 12;
      CostMulDistrib(i - st, 1, i - st + 1, C1);
      i := i + 1;
    }
    CostMulMonoLeft(i - st, M, C1);
    if temp > res { res := temp; }
    steps := steps + 12;
    CostMulDistrib(st, 1, st + 1, C2);
    st := st + 1;
  }
  CostMulMonoLeft(st, M, C2);
  if mx > res { res := mx; }

  steps := steps + 4;
  var scaled := (res * 1000000000000.0 + 0.5).Floor;
  var digits := IntToString(scaled);
  IntToStringDigits(scaled);
  steps := steps + Digits(scaled);
  ghost var d0 := |digits|;
  ghost var s2 := steps;
  while |digits| < 13
    invariant |digits| >= d0
    invariant |digits| <= 13 || |digits| == d0
    invariant steps <= s2 + 20 * (|digits| - d0)
  { digits := "0" + digits; steps := steps + 20; }
  steps := steps + 260;
  var intStr := digits[..|digits| - 12];
  var fracStr := digits[|digits| - 12..];
  output := intStr + "." + fracStr + "\n";
  steps := steps + |output| + 10;
}
