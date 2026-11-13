include "../../../prelude.dfy"
import opened Prelude

ghost function Dg(b: int): nat { if b > 0 then Digits(b) else 1 }
ghost function K1f(D: nat): nat { 6 * D + 6 }
ghost function K2f(D: nat): nat { 6 * D + D * K1f(D) + 20 }
ghost function Mf(a: int, b: int): nat { if b >= a then b - a + 1 else 0 }

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= Mf(a, b) * K2f(Dg(b)) + 5 + |output|
{
  steps := 1;
  ghost var D := Dg(b);
  ghost var K1 := K1f(D);
  ghost var K2 := K2f(D);
  var found := false;
  var ans := 0;
  var i := a;
  while i <= b && !found
    invariant a <= i <= (if b >= a then b + 1 else a)
    invariant steps <= 1 + (i - a) * K2
    decreases b - i + 1
  {
    var temp := i;
    var digits: seq<int> := [];
    ghost var ls := 0;
    while temp > 0
      invariant i <= 0 ==> |digits| == 0
      invariant i > 0 ==> |digits| + (if temp > 0 then Digits(temp) else 0) == Digits(i)
      invariant i > 0 ==> temp >= 0
      invariant ls <= 6 * |digits|
      decreases temp
    {
      ls := ls + 6;
      digits := digits + [temp % 10];
      temp := temp / 10;
    }
    var distinct := true;
    var p := 0;
    if i > 0 { DigitsMono(i, b); }
    assert |digits| <= D;
    ghost var le := ls;
    while p < |digits|
      invariant 0 <= p <= |digits|
      invariant ls <= le + p * K1
      decreases |digits| - p
    {
      ghost var lp := ls;
      var q := p + 1;
      while q < |digits|
        invariant p < q <= |digits|
        invariant ls <= lp + 6 * q
        decreases |digits| - q
      {
        ls := ls + 6;
        if digits[p] == digits[q] { distinct := false; }
        q := q + 1;
      }
      CostMulDistrib(p, 1, p + 1, K1);
      ls := ls + 6;
      p := p + 1;
    }
    CostMulMonoLeft(p, D, K1);
    steps := steps + ls + 12;
    if distinct {
      found := true;
      ans := i;
    }
    CostMulDistrib(i - a, 1, i - a + 1, K2);
    i := i + 1;
  }
  CostMulMonoLeft(i - a, Mf(a, b), K2);
  if found {
    output := IntToString(ans);
    IntToStringDigits(ans);
    steps := steps + Digits(ans);
  } else {
    output := "-1";
  }
}
