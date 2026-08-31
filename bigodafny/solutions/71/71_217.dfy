// 454_B. Little Pony and Sort by Shift  (problem 71, solution 71_217)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// #for x in range(len(a)):
// #    a[x]=int(a[x])
// # print(x)
// ans=0
// d=0
// for x in range(1,n):
//     if(a[x-1]>a[x]):
//         d=1
//         if(sorted(a)==a[x:]+a[:x]):
//             ans=n-x
//         else:
//             ans=-1
//         break
// if(d==0):
//     print(0)
// else:
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
