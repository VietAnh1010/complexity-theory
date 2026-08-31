// 1144_D. Equalize Them All  (problem 397, solution 397_163)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import collections
// 
// def solve():
//     N=int(input())
//     A=list(map(int,input().split()))
//     c=collections.Counter(A)
//     max_count = sorted(c.values(), reverse=True)[0]
//     max_key = [k for k in c.keys() if c[k] == max_count][0]
//     pivot = A.index(max_key)
//     ans=[]
//     for i in range(pivot-1, -1, -1):
//         if A[i]<max_key:
//             ans.append([1,i+1,i+2])
//         else:
//             ans.append([2,i+1,i+2])
//     #print(max_key,pivot)
//     for i in range(pivot+1, N):
//         if A[i]==max_key:
//             continue
//         if A[i]<max_key:
//             ans.append([1,i+1,i])
//         else:
//             ans.append([2,i+1,i])
//     print(len(ans))
//     for a in ans:
//         print(' '.join(list(map(str,a))))
// 
// solve()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
