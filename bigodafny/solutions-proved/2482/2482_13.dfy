include "../../prelude.dfy"
import opened Prelude

lemma MulAtLeast(n: int, a: int)
  requires n >= 0 && a >= 1
  ensures n * a >= n
{
  assert n * a == n * (a - 1) + n;
  assert n * (a - 1) >= 0;
}

method Solve(N: int, M: int) returns (output: string, ghost steps: nat)
  requires N >= 2
  ensures steps <= 6 * (if M > 0 then M else 0) + 4 + |output|
{
  steps := 1;
  var n := 0;
  while n * (N - 1) + 1 < M
    invariant n >= 0
    invariant n <= (if M > 0 then M else 0)
    invariant steps <= 6 * n + 1
    decreases M - n
  {
    MulAtLeast(n, N - 1);
    n := n + 1;
    steps := steps + 6;
  }
  steps := steps + 3;
  output := IntToString(n);
  IntToStringDigits(n);
  steps := steps + Digits(n);
}
