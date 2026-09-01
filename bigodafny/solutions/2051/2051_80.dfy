// p03948 AtCoder Regular Contest 063 - An Invisible Hand  (problem 2051, solution 2051_80)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/usr/bin python3
// # -*- coding: utf-8 -*-
// 
// import bisect
// 
// n, t = map(int, input().split())
// a = list(map(int, input().split()))
// mx = 0
// p = [0] * n
// for i in range(n-1,-1,-1):
//     mx = max(mx, a[i])
//     p[i] = mx - a[i]
// p.sort()
// print(n-bisect.bisect_left(p, p[-1]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
{
  var a := numbers;
  var mx := 0;
  var p: seq<int> := seq(n, idx requires 0 <= idx < n => 0);
  var i := n - 1;
  while i >= 0
    decreases i + 1
  {
    if a[i] > mx { mx := a[i]; }
    p := p[i := mx - a[i]];
    i := i - 1;
  }
  var sortedP := SortInts(p);
  var target := sortedP[|sortedP| - 1];
  var lo := 0;
  while lo < |sortedP| && sortedP[lo] < target
    decreases |sortedP| - lo
  {
    lo := lo + 1;
  }
  output := IntToString(n - lo);
}
