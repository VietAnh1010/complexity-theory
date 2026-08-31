// p02721 AtCoder Beginner Contest 161 - Yutori  (problem 1369, solution 1369_10)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N,K,C=map(int,input().split())
// S=input()
// L=[0 for i in range(K)]
// R=[0 for i in range(K)]
// n=0
// rc=0
// lc=0
// while True:
//   if lc==K:
//     break
//   if S[n]=="o":
//     L[lc]=n+1
//     n+=C+1
//     lc+=1
//   else:
//     n+=1
// n=N-1
// while True:
//   if rc==K:
//     break
//   if S[n]=="o":
//     R[K-1-rc]=n+1
//     n-=C+1
//     rc+=1
//   else:
//     n-=1
// for i in range(K):
//   if R[i]==L[i]:
//     print(R[i])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
