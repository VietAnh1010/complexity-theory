// 18_D. Seller Bob  (problem 2942, solution 2942_55)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=int(input())
// a={}
// sum=[]
// ls=-1
// for i in range(s):
//   sum.append(0)
// for i in range(s):
//   n, z = map(str, input().split())
//   m=int(z)
//   if(n=="win"):
//       a[m]=(1,i)
//   if (n=="sell"):
//     p = a.get(m, -1)
//     if(p!=-1):
//       if(sum[i-1]<2**m+sum[a[m][1]]):
//         sum[i]=2**m+sum[a[m][1]]
//         ls=i
//       else:
//         if(a[m][1]>ls):
//           sum[i]=2**m+sum[i-1]
//           ls=i
//   if(sum[i]==0):
//     sum[i]=sum[i-1]
// print(sum[s-1])
// 
// # Sun Mar 24 2019 13:38:31 GMT+0300 (MSK)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, transactions: seq<seq<string>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
