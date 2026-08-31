// 788_A. Functions again  (problem 2198, solution 2198_52)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// 
// b = []
// for i in range(n - 1):
//     b.append(abs(a[i] - a[i + 1]))
// 
// c = []
// s = 1
// summ = 0
// for i in range(n - 1):
//     summ += s * b[i]
//     s = -s
//     c.append(summ)
// 
// c.sort()
// 
// if c[0] < 0:
//     print(c[n - 2] - c[0])
// else:
//     print(c[n - 2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
