// 1051_C. Vasya and Multisets  (problem 2005, solution 2005_187)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import *
// n = int(input())
// a = list(map(int,input().split()))
// ans = ["A"]*n
// num = 0
// for i in range(n):
//     if a.count(a[i])>1:
//         continue
//     if num<0:
//         num+=1
//         ans[i] = "B"
//     else:
//         num-=1
// if num<0:
//     for i in range(n):
//         if a.count(a[i])<=2:
//             continue
//         ans[i] = "B"
//         num= 0
//         break
// if num==0:
//     print("YES")
//     print(*ans,sep = '')
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
