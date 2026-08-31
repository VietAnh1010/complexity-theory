// p03938 AtCoder Grand Contest 007 - Construct Sequences  (problem 1981, solution 1981_39)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// p = list(map(int, input().split()))
// 
// a = [i*40000+1 for i in range(n)]
// b = a[:]
// b.reverse()
// 
// for i in range(n):
//     b[p[i]-1] += i+1
// print(*a)
// print(*b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
