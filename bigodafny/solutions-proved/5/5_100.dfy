// 622_A. Infinite Sequence  (problem 5, solution 5_100)
// time complexity: O(sqrt(n))
// label corrected 2026-10-20: BigOBench says O(n); this proof bounds steps by 4 * ISqrt(2 * n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// k=1
// while(n>k):
//    n-=k
//    k+=1
// print(n)
//    
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * ISqrt(2 * n) + |output| + 1
{
  steps := 0;
  var m, k := n, 1;
  while m > k
    invariant k >= 1
    invariant 2 * (n - m) == (k - 1) * k
    invariant steps == 4 * (k - 1)
    invariant k == 1 || (k - 1) * (k - 1) <= 2 * n
    decreases m - k
  {
    assert k * k <= (k - 1) * k + 2 * k;
    steps := steps + 2;
    steps := steps + 1;
    m := m - k;
    steps := steps + 1;
    k := k + 1;
  }
  if k > 1 {
    LeISqrt(k - 1, 2 * n);
  }
  IntToStringDigits(m);
  steps := steps + 1;
  steps := steps + (Digits(m) + |"\n"|);
  output := IntToString(m) + "\n";
}

