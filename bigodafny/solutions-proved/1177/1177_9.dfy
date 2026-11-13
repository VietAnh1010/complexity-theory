include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<(int, int)>, m: int, checks: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires n == |rectangles|
  requires m == |checks|
  requires n >= 1
  requires m >= 1
  ensures steps <= 2 * NLogN(n) + 2 * NLogN(m) + 8 * n + 8 * m + 10 + |output|
{
  steps := 1;
  var c := Sort(rectangles, (p: (int,int), q: (int,int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1));
  var p := Sort(checks, (a: (int,int), b: (int,int)) => a.0 < b.0 || (a.0 == b.0 && a.1 < b.1));
  steps := steps + SortCost(n) + SortCost(m);
  SortCostNLogN(n);
  SortCostNLogN(m);
  var ans := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + SortCost(n) + SortCost(m) + 8 * i
    decreases n - i
  {
    var cand := p[m-1].0 - c[i].1;
    if cand > ans { ans := cand; }
    i := i + 1;
    steps := steps + 8;
  }
  i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant steps <= 1 + SortCost(n) + SortCost(m) + 8 * n + 8 * i
    decreases m - i
  {
    var cand := c[n-1].0 - p[i].1;
    if cand > ans { ans := cand; }
    i := i + 1;
    steps := steps + 8;
  }
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + Digits(ans) + 2;
}
