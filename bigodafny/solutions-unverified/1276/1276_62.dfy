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
    decreases partCount - q
  {
    ws[q] := wsPart[q];
    q := q + 1;
  }
  while q < m
    decreases m - q
  {
    ws[q] := 1;
    q := q + 1;
  }

  var dp := new int[m];
  q := 0;
  while q < m
    decreases m - q
  {
    dp[q] := ws[q];
    q := q + 1;
  }

  var rep := 0;
  while rep < k - 1
    decreases k - 1 - rep
  {
    var newdp := new int[m];
    var acc := 0;
    var t := 0;
    while t < m
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
    decreases m - t2
  {
    ans := (ans + dp[t2]) % md;
    t2 := t2 + 1;
  }
  output := IntToString(ans);
}
}
