// 1095_D. Circular Dance  (problem 2007, solution 2007_136)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=[]
// a,b=0,0
// for i in range(n):
//     s=list(map(int,input().split(" ")))
//     a=int(s[0])
//     b=int(s[1])
//     l.append([a,b])
// ans=[1]
// a,b=l[0][0],l[0][1]
// if b in l[a-1]:
//     ans.append(a)
//     ans.append(b)
//     i=a
//     j=b
// else:
//     ans.append(b)
//     ans.append(a)
//     i=b
//     j=a
// while len(ans)<n:
//     for c in l[i-1]:
//         if c!=j:
//             ans.append(c)
//             break
//     i=j
//     j=c
// q=''
// q+=str(ans[0])
// for i in range(1,n):
//     q+=' '+str(ans[i])
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
