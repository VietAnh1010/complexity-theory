// 1144_D. Equalize Them All  (problem 397, solution 397_80)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// n=int(input())
// l=list(map(int,input().split()))
// c,f=Counter(l).most_common(1)[0]
// a=int(l.index(c))
// print(n-f)
// for i in range(a-1,-1,-1):
//     if l[i]!=c:
//         print(1 if l[i]<c else 2,i+1,i+2)
// for i in range(a+1,len(l)):
//     if l[i]!=c:
//         print(1 if l[i]<c else 2,i+1,i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
