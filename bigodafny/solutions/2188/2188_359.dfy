// 1365_C. Rotation Matching  (problem 2188, solution 2188_359)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int,input().split()))
// b = list(map(int,input().split()))
// dif = [0]*n
// a = list(enumerate(a))
// b = list(enumerate(b))
// a.sort(key = lambda x:x[1])
// b.sort(key = lambda x:x[1])
// for i in range(n):
//     q1 = a[i][0]
//     q2 = b[i][0]
//     if q2-q1<0:
//         dif[i]=(n+(q2-q1))
//     else:
//         dif[i]=(q2-q1)
// maxi = 0
// difmax = [0]*n
// for s in dif:
//     difmax[s]+=1
//     if difmax[s]>maxi:
//         maxi = difmax[s]
// print(maxi)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
