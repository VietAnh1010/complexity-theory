// p02992 AtCoder Beginner Contest 132 - Small Products  (problem 1276, solution 1276_62)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from itertools import accumulate
// 
// def f(n,k):
//     lim = int((n + 0.1) ** 0.5) + 1
//     ws = []
//     s = 0
//     for i in range(1, lim):
//         w = n // i - n // (i + 1)
//         ws.append(w)
//         s += w
//     ws += [1] * (n - s)
//     dp=ws
//     m = len(ws)
//     for _ in range(k - 1):
//         dp=[s*w%md for s,w in zip(accumulate(dp[::-1]),ws)]
//     print(sum(dp) % md)
// md=10**9+7
// n,k=map(int,input().split())
// f(n,k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma ExtraLe(n: int, r: nat, e: int)
  requires n >= 0 && r == ISqrt(n) && e == n / (r + 1)
  ensures e <= r
{
  ISqrtSpec(n);
  assert n < (r + 1) * (r + 1);
  assert e <= r by {
    if e > r {
      assert e * (r + 1) >= (r + 1) * (r + 1) by { CostMulMonoLeft(r + 1, e, r + 1); }
      assert e * (r + 1) <= n;
    }
  }
}

lemma MulBound(rep: nat, K: nat, x: nat, y: nat)
  requires rep <= K && x <= y
  ensures rep * x <= K * y
{
  CostMulMonoLeft(rep, K, x);
  CostMulMono(K, x, y);
}

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  // 4 of 103 stored inputs give a < 0; all four make the row's own Python
  // raise while parsing, so there is no behaviour there to reproduce.
  requires a >= 0
  ensures steps <= ISqrtSteps(a) + 40 * (ISqrt(a) + 1) + (if b > 1 then b - 1 else 0) * (16 * (ISqrt(a) + 1)) + |output|
{
{
  var n := a;
  var k := b;
  var md := 1000000007;
  var r := ISqrt(n);
  steps := ISqrtSteps(n) + 3;
  var lim := r + 1;
  var partCount := lim - 1;
  var wsPart := new int[partCount];
  steps := steps + partCount;
  var s := 0;
  var i := 1;
  while i < lim
    invariant 1 <= i <= lim
    invariant wsPart.Length == partCount
    invariant s == n - n / i
    invariant steps == ISqrtSteps(n) + 3 + partCount + 8 * (i - 1)
    decreases lim - i
  {
    var w := n / i - n / (i + 1);
    wsPart[i-1] := w;
    s := s + w;
    i := i + 1;
    steps := steps + 8;
  }
  var extra := n - s;
  assert extra == n / lim;
  ExtraLe(n, r, extra);
  var m := partCount + extra;
  var ws := new int[m];
  var q := 0;
  ghost var base := steps + 2 + m;
  steps := base;
  while q < partCount
    invariant 0 <= q <= partCount
    invariant ws.Length == m && wsPart.Length == partCount && partCount <= m
    invariant steps == base + 3 * q
    decreases partCount - q
  {
    ws[q] := wsPart[q];
    q := q + 1;
    steps := steps + 3;
  }
  while q < m
    invariant 0 <= q
    invariant ws.Length == m
    invariant partCount <= q
    invariant steps == base + 3 * q
    decreases m - q
  {
    ws[q] := 1;
    q := q + 1;
    steps := steps + 3;
  }

  var dp := new int[m];
  steps := steps + m;
  q := 0;
  ghost var base2 := steps;
  while q < m
    invariant 0 <= q
    invariant ws.Length == m && dp.Length == m
    invariant steps == base2 + 3 * q
    decreases m - q
  {
    dp[q] := ws[q];
    q := q + 1;
    steps := steps + 3;
  }

  var rep := 0;
  ghost var base3 := steps;
  while rep < k - 1
    invariant ws.Length == m && dp.Length == m
    invariant 0 <= rep
    invariant steps <= base3 + rep * (7 * m + 4)
    decreases k - 1 - rep
  {
    var newdp := new int[m];
    ghost var st := steps + m;
    var acc := 0;
    var t := 0;
    while t < m
      invariant 0 <= t
      invariant ws.Length == m && dp.Length == m && newdp.Length == m
      invariant st == steps + m + 6 * t
      decreases m - t
    {
      acc := (acc + dp[m-1-t]) % md;
      newdp[t] := (acc * ws[t]) % md;
      t := t + 1;
      st := st + 6;
    }
    dp := newdp;
    rep := rep + 1;
    CostMulDistrib(rep - 1, 1, rep, 7 * m + 4);
    steps := st + 4;
  }

  var ans := 0;
  var t2 := 0;
  ghost var base4 := steps;
  while t2 < m
    invariant 0 <= t2
    invariant dp.Length == m
    invariant steps == base4 + 4 * t2
    decreases m - t2
  {
    ans := (ans + dp[t2]) % md;
    t2 := t2 + 1;
    steps := steps + 4;
  }
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + Digits(ans);

  ghost var K := if k > 1 then k - 1 else 0;
  MulBound(rep, K, 7 * m + 4, 16 * (r + 1));
}
}
