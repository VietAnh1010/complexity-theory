include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= |s| * (26 * (|s| + 12) + 5) + 26 * (|s| + 12) + 10 + |output|
{
  steps := 1;
  ghost var M: nat := |s| + 12;
  ghost var K: nat := 26 * M + 5;
  var d: set<string> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant steps <= 1 + i * K
    decreases |s| - i
  {
    var a := 0;
    ghost var s0 := steps;
    while a < 26
      invariant 0 <= a <= 26
      invariant steps <= s0 + a * M
      decreases 26 - a
    {
      var ch := ((('a' as int) + a) as char);
      d := d + {s[..i] + [ch] + s[i..]};
      a := a + 1;
      steps := steps + M;
      CostMulDistrib(a - 1, 1, a, M);
    }
    i := i + 1;
    steps := steps + 5;
    CostMulDistrib(i - 1, 1, i, K);
  }
  var a2 := 0;
  ghost var s1 := steps;
  while a2 < 26
    invariant 0 <= a2 <= 26
    invariant steps <= s1 + a2 * M
    decreases 26 - a2
  {
    var ch := ((('a' as int) + a2) as char);
    d := d + {s + [ch]};
    a2 := a2 + 1;
    steps := steps + M;
    CostMulDistrib(a2 - 1, 1, a2, M);
  }
  output := IntToString(|d|);
  IntToStringDigits(|d|);
  steps := steps + Digits(|d|);
  CostMulMonoLeft(i, |s|, K);
}
