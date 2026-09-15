// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `lim` is set via `while (r+1)*(r+1)<=n` so lim ~ sqrt(n), and `m :=
//     partCount+extra` with extra = n - s = n/lim per the loop invariant,
//     making the ws/dp arrays size O(sqrt(n)); the `while rep<k-1` loop
//     repeats the O(m) inner scan up to k-1 times, giving O(k*sqrt(n))
//     (real class) versus the label's O(n+m), and the Python's `lim =
//     int((n+0.1)**0.5)+1` computes the identical bound.
//
//   how this label could be wrong, and what to check:
//     The label O(n+m) assumes the ws/dp arrays scale with n. Check the
//     invariant `s == n - n/i` at the exit of the `while i<lim` loop: it
//     implies extra = n - s = n/lim, and lim ~ sqrt(n), so m :=
//     partCount+extra is O(sqrt(n)), not O(n); the `while rep<k-1` loop
//     then does O(m) work k-1 times.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 94, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 8, "recursive_helpers": 0, "seq_append_read_in_same_loop":
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
  var r := 0;
  while (r+1)*(r+1) <= n
    decreases n - r*r
  {
    r := r + 1;
  }
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
