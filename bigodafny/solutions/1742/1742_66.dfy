// p03214 Dwango Programming Contest V - Thumbnail  (problem 1742, solution 1742_66)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// mean=sum(a)/n
// a=[abs(i-mean) for i in a]
// b=[]
// for i in range(n):
//     b.append([a[i],i])
// b.sort()
// print(b[0][1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
