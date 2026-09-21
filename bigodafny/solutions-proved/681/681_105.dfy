// p03683 AtCoder Regular Contest 076 - Reconciled?  (problem 681, solution 681_105)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// mod=10**9+7
//
//
// def main():
//     n, m = map(int, input().split())
//     if abs(n - m) > 1:
//         return 0
//
//
//     fact = 1
//     for i in range(1, min(n, m) + 1):
//         fact = fact * i % mod
//
//
//
//     if n == m:
//         return fact ** 2 * 2 % mod
//     else:
//         return fact * fact * (min(n, m) + 1) % mod
//
//
//
//
// print(main())
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * (if a > 0 then a else 0) + 4 * (if b > 0 then b else 0) + 10
{
  steps := 1;
  var mod := 1000000007;
  if a - b > 1 || b - a > 1 {
    output := IntToString(0);
    steps := steps + 2;
  } else {
    var mn := if a < b then a else b;
    var fact := 1;
    var i := 1;
    while i <= mn
      invariant i == 1 || i <= mn + 1
      invariant 1 <= i
      invariant steps <= 2 * i - 1
      decreases mn - i + 1
    {
      fact := (fact * i) % mod;
      i := i + 1;
      steps := steps + 2;
    }
    if a == b {
      output := IntToString((fact * fact % mod) * 2 % mod);
    } else {
      output := IntToString((fact * fact % mod) * (mn + 1) % mod);
    }
    steps := steps + 3;
  }
}
