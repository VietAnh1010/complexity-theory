// 1042_A. Benches  (problem 61, solution 61_161)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// m = int(input())
// 
// a = []
// _sum = 0
// for i in range(n):
//     j = int(input())
//     a.append(j)
//     _sum += j
// #print(a)
// a = sorted(a)
// if n == 1:
//     print(m + a[0], m + a[0])
// else:
//     _max = m + a[-1]
//     temp = a[-1] * n
//     if temp- _sum >= m:
//         print(a[-1], _max)
//     else:    
//         m -= temp - _sum
//         _min = a[-1] + (int(m / n))
//         if m % n != 0:
//             _min += 1
//         print(_min, _max)
//     
// 
//     
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, ignored_lines: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
