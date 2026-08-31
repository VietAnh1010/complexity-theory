// 426_A. Sereja and Mugs  (problem 3070, solution 3070_180)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,s=map(int,input().split())
// l=list(map(int,input().split()))
// l.sort()
// sum1=0
// for i in range(n-1):
// 	sum1+=l[i]
// if sum1<=s:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
