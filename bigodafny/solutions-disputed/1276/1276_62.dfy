// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's `ws` has `partCount + extra` entries, both about
//     sqrt(n), and the `while rep < k - 1` loop sweeps all of them each
//     round, so the cost is O(k sqrt n); the Python's `accumulate` loop is
//     the same.
//
//   how this label could be wrong, and what to check:
//     The label sums n and k, but the DP runs k - 1 rounds over a weight
//     list of length about 2*sqrt(n): `lim` is sqrt(n) and the padding `n
//     - s` equals n // lim, also about sqrt(n). Check the length m of
//     `ws`; the class is O(k sqrt n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 89, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 7, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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

method Solve(a: int, b: int) returns (output: string)
  // 4 of 103 stored inputs give a < 0; all four make the row's own Python
  // raise while parsing, so there is no behaviour there to reproduce.
  requires a >= 0
{
{

  var n := a;
  var k := b;
  var md := 1000000007;
  var r := ISqrt(n);
  var lim := r + 1;
  var partCount := lim - 1;
  var wsPart := new int[partCount];
  var s := 0;
  var i := 1;
  while i < lim
    invariant 1 <= i <= lim
    invariant wsPart.Length == partCount
    // the terms telescope: sum_{j<i} (n/j - n/(j+1)) == n - n/i
    invariant s == n - n / i
    decreases lim - i
  {
    var w := n / i - n / (i + 1);
    wsPart[i-1] := w;
    s := s + w;
    i := i + 1;
  }
  var extra := n - s;
  var m := partCount + extra;
  var ws := new int[m];
  var q := 0;
  while q < partCount
    invariant 0 <= q <= partCount
    invariant ws.Length == m && wsPart.Length == partCount && partCount <= m
    decreases partCount - q
  {
    ws[q] := wsPart[q];
    q := q + 1;
  }
  while q < m
    invariant 0 <= q
    invariant ws.Length == m
    decreases m - q
  {
    ws[q] := 1;
    q := q + 1;
  }

  var dp := new int[m];
  q := 0;
  while q < m
    invariant 0 <= q
    invariant ws.Length == m && dp.Length == m
    decreases m - q
  {
    dp[q] := ws[q];
    q := q + 1;
  }

  var rep := 0;
  while rep < k - 1
    invariant ws.Length == m && dp.Length == m
    decreases k - 1 - rep
  {
    var newdp := new int[m];
    var acc := 0;
    var t := 0;
    while t < m
      invariant 0 <= t
      invariant ws.Length == m && dp.Length == m && newdp.Length == m
      decreases m - t
    {
      acc := (acc + dp[m-1-t]) % md;
      newdp[t] := (acc * ws[t]) % md;
      t := t + 1;
    }
    dp := newdp;
    rep := rep + 1;
  }

  var ans := 0;
  var t2 := 0;
  while t2 < m
    invariant 0 <= t2
    invariant dp.Length == m
    decreases m - t2
  {
    ans := (ans + dp[t2]) % md;
    t2 := t2 + 1;
  }
  output := IntToString(ans);
}
}
