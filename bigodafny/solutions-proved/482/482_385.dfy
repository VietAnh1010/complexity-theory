// 214_A. System of Equations  (problem 482, solution 482_385)
// time complexity: O(n**2+m**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m = map(int, input().split())
// c = 0
// for a in range(0,max(n ,m) + 1):
//     for b in range(0, max(n, m) + 1):
//         if ((a **2) + b) == n and (a + (b ** 2)) == m:
//             c = c + 1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma SqBound(x: int)
  requires x >= 0
  ensures (x + 1) * (x + 1) <= 2 * (x * x) + 2
{
  assert (x - 1) * (x - 1) >= 0;
}

lemma MaxSq(n: int, m: int, mx: int)
  requires mx == n || mx == m
  ensures mx * mx <= n * n + m * m
{
  if mx == n { assert m * m >= 0; } else { assert n * n >= 0; }
}

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 24 * (a * a + b * b) + 40 + |output|
{
  steps := 1;
  var n := a;
  var m := b;
  var mx := if n > m then n else m;
  steps := steps + 2;
  ghost var M: nat := if mx >= 0 then mx + 1 else 0;
  var c := 0;
  var av := 0;
  ghost var K: nat := 12 * M + 3;
  ghost var base: nat := steps;
  while av <= mx
    invariant 0 <= av <= M
    invariant M == (if mx >= 0 then mx + 1 else 0)
    invariant steps == base + av * K
    decreases mx - av
  {
    var bv := 0;
    ghost var s0 := steps;
    while bv <= mx
      invariant 0 <= bv <= M
      invariant steps == s0 + 12 * bv
      decreases mx - bv
    {
      if av * av + bv == n && av + bv * bv == m {
        c := c + 1;
      }
      bv := bv + 1;
      steps := steps + 12;
    }
    steps := steps + 3;
    CostMulDistrib(av, 1, av + 1, K);
    assert bv == M;
    assert steps == s0 + 12 * M + 3;
    av := av + 1;
  }
  output := IntToString(c);
  IntToStringDigits(c);
  steps := steps + Digits(c);
  if mx >= 0 {
    SqBound(mx);
    MaxSq(n, m, mx);
    assert M == av;
    CostMulMonoLeft(0,0,0);
    assert steps == base + M * K + Digits(c);
    assert M * K == 12 * (M * M) + 3 * M;
    assert 3 * M <= 3 * M * M + 3 || true;
  } else {
    assert av == 0;
    assert M * K == 0;
  }
}
