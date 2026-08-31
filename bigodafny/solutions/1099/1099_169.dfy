// 937_A. Olympiad  (problem 1099, solution 1099_169)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// a.sort()
// if (a[0]!=0): res = 1
// else: res = 0
// b = a[0]
// for i in range(len(a)):
//     if (a[i]!=b): res+=1
//     b = a[i]
// print(str(res))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
