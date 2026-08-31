// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_134)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// x = []
// y = []
// for i in range(n):
//     xi, yi = map(int, input().split())
//     x.append(xi)
//     y.append(yi)
// if n==1:
//     print(-1)
// 
// if n>=2:
//     s = (max(x) - min(x)) * (max(y) - min(y))
//     if s == 0: s = -1
//     print(s)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<seq<string>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
