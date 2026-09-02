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
  var l := SortInts(a_list);
  var sum1 := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i
    decreases (n - 1) - i
  {
    if i < |l| {
      sum1 := sum1 + l[i];
    }
    i := i + 1;
  }
  if sum1 <= m {
    output := "YES";
  } else {
    output := "NO";
  }
}
