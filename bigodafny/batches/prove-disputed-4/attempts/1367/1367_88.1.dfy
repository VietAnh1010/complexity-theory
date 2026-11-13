include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires n == |coordinates|
  ensures steps <= 12 * n + 8 + |output|
  requires forall idx :: 1 <= idx < n ==> 0 <= coordinates[idx] <= idx
{
  steps := n + 2;
  var b := seq(n + 1, i => 0);
  var res := 1;
  if n >= 1 {
    b := b[1 := 1];
    steps := steps + 2;
  }
  var i := 2;
  while i <= n
    invariant 2 <= i
    invariant |b| == n + 1
    invariant steps <= n + 4 + 12 * (i - 2)
    decreases n - i
  {
    var key := coordinates[i - 1];
    if b[key] == 0 {
      b := b[i := 1];
      res := res + 1;
    } else {
      b := b[i := 1];
      b := b[key := 0];
    }
    i := i + 1;
    steps := steps + 12;
  }
  output := IntToString(res);
  IntToStringDigits(res);
  steps := steps + Digits(res);
}
