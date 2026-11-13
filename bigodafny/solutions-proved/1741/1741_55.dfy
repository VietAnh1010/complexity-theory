include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, scores: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * |scores| + 3 + |output|
{
  steps := 1;
  var m := 0;
  var c := 0;
  var i := 0;
  while i < |scores|
    invariant 0 <= i <= |scores|
    invariant steps <= 6 * i + 1
    decreases |scores| - i
  {
    if m <= scores[i] {
      m := scores[i];
      c := c + 1;
    }
    i := i + 1;
    steps := steps + 6;
  }
  output := IntToString(c);
  IntToStringDigits(c);
  steps := steps + Digits(c);
}
