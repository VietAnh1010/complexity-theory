// 545_C. Woodcutters  (problem 1560, solution 1560_63)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// inf = 10**18
// a=[]
// n = int(input())
// for i in range(n):
//     a.append([int(i) for i in input().split()])
// a.sort()
// occ = [a[0][0]-a[0][1],a[0][0]]
// ans=1
// for j in range(1,n):
//     i=a[j][:]
//     cur1=[i[0]-i[1],i[0]]
//     cur2=[i[0],i[0]+i[1]]
//     if occ[1]<cur1[0]:
//         occ[1]=cur1[1]
//         ans+=1
//     elif occ[1]<cur2[0] and (j+1==n or(j+1<n and cur2[1]<a[j+1][0])):
//         occ[1]=cur2[1]
//         ans+=1
//     else:
//         occ[1]=i[0]
// print(ans)
//     
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
