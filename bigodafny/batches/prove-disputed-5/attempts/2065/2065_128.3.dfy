include "../../prelude.dfy"
import opened Prelude

ghost function Pos(x: int): nat { if x < 0 then 0 else x }

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= (ISqrt(n * 2) + 2) * (CeilLog2(Pos(n * 2)) + 12) + CeilLog2(Pos(n * 2)) + 10
{
  var a := n * 2;
  ghost var K := CeilLog2(Pos(a)) + 12;
  ISqrtStepsBound(a);
  steps := ISqrtSteps(a) + 4;
  var b := 0;

  var lim: int := ISqrt(a);

  var i := 1;
  while i < lim
    invariant 1 <= i <= lim + 1
    invariant steps <= CeilLog2(Pos(a)) + 10 + i * K
    decreases lim - i
  {
    var c := a - i * i - i;
    assert i * i >= 0 by { CostMulMono(i, 0, i); }
    CostMulDistrib(i, 1, i + 1, K);
    steps := steps + 5;
    if c >= 0 {
      var d := ISqrt(c);
      ISqrtStepsBound(c);
      CeilLog2Monotone(Pos(c), Pos(a));
      steps := steps + ISqrtSteps(c) + 5;
      if d * (d + 1) == c {
        b := 1;
      }
    }
    i := i + 1;
  }
  CostMulMonoLeft(i, ISqrt(a) + 2, K);
  steps := steps + 1;

  if b == 1 {
    output := "YES";
  } else {
    output := "NO";
  }
}
