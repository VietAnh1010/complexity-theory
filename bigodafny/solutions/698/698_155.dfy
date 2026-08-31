// 330_B. Road Construction  (problem 698, solution 698_155)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// func = lambda: map(int, input().split())
// n, m = func()
// a = set(range(1, n+1))
// for _ in range(m): a-=set(func())
// a = list(a)[0]
// print(n-1)
// for i in range(1, n+1):
//     if i!=a: print(i, a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, q: int, queries: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
