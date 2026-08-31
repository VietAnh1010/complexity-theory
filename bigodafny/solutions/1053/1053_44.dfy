// 605_A. Sorting Railway Cars  (problem 1053, solution 1053_44)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// p=list(map(int,input().split()))
// for i in range(n):
//     p[i]=[p[i],i]
// p.sort()
// b=1
// d=[]
// for i in range(n-1):
//     if p[i][1]<p[i+1][1]:
//         b+=1
//     else:
//         d.append(b)
//         b=1
// d.append(b)
// print(n-max(d))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
