// 1299_A. Anu Has a Function  (problem 2465, solution 2465_212)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// a = [int(x) for x in input().split()]
// 
// a.sort(reverse=True)
// 
// mask = 2**30
// while mask and len([ai for ai in a if ai & mask])!=1:
//     mask>>=1
// for i in range(n):
//     if mask&a[i]:
//         break
// a[i], a[0] = a[0], a[i]
// print (*a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
