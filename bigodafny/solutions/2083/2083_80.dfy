// 1107_C. Brutality  (problem 2083, solution 2083_80)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// l=list(map(int,input().split()))
// s=str(input())
// t=0
// i=0
// while(i<n):
//     j=i
//     p=[]
//     while(j<n and s[i]==s[j]):
//         p.append(l[j])
//         j+=1
//     p.sort(reverse=True)
//     c=min(k,len(p))
//     t=t+sum(p[0:c])
//     i=j
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
