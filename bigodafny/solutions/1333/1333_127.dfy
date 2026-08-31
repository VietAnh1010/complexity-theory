// 1029_C. Maximal Intersection  (problem 1333, solution 1333_127)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// L = []
// R = []
// S = []
// for _ in range(n):
//     a,b = [int(x) for x in input().split()]
//     L.append(a)
//     R.append(b)
//     S.append((a,b))
// 
// 
// L.sort(reverse = True)
// R.sort()
// 
// if (L[0],R[0]) in S:
//     print(max(R[1]-L[1],0))
// else:
//     print(max(R[0]-L[1],R[1]-L[0],0))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
