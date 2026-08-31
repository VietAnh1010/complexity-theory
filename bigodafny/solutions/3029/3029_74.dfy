// p03714 AtCoder Beginner Contest 062 - 3N Numbers  (problem 3029, solution 3029_74)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import heapq
// 
// N=int(input())
// A=list(map(int,input().split()))
// 
// R=sorted(A[:N])
// SUM1=[sum(A[:N])]
// for i in range(N,2*N):
//     heapq.heappush(R,A[i])
//     tmp=heapq.heappop(R)
//     SUM1.append(SUM1[-1]+A[i]-tmp)
// 
// B=list(map(lambda x:x*(-1),A[2*N:3*N]))
// B.sort()
// SUM2=[-sum(B)]
// for i in range(2*N-1,N-1,-1):
//     heapq.heappush(B,-A[i])
//     tmp=heapq.heappop(B)
//     SUM2.append(SUM2[-1]+A[i]+tmp)
// 
// ans=-float("inf")
// for i in range(N+1):
//     ans=max(ans,SUM1[i]-SUM2[-(i+1)])
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, digits: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
