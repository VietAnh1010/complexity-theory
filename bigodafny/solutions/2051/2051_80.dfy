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
  output := ""; // TODO: translate the Python above
}
