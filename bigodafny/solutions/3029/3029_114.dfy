// p03714 AtCoder Beginner Contest 062 - 3N Numbers  (problem 3029, solution 3029_114)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import heapq
// N=int(input())
// a=list(map(int,input().split()))
// l=[None]*(N+1)
// r=[None]*(N+1)
// h=a[:N]
// s=sum(h)
// heapq.heapify(h)
// l[0]=s
// for i in range(N):
//     heapq.heappush(h,a[i+N])
//     s+=a[i+N]-heapq.heappop(h)
//     l[i+1]=s
// h=list(map(lambda x:-x,a[2*N:]))
// heapq.heapify(h)
// s=sum(h)
// r[-1]=s
// for i in range(N):
//     heapq.heappush(h,-a[-N-i-1])
//     s+=-a[-N-i-1]-heapq.heappop(h)
//     r[-i-2]=s
// a=l[0]+r[0]
// for i in range(1,N+1):
//     if a<l[i]+r[i]:
//         a=l[i]+r[i]
// print(a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, digits: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
