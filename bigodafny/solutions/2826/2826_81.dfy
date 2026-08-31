// 608_C. Chain Reaction  (problem 2826, solution 2826_81)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys,bisect
// n=int(input())
// a,b=[],[]
// for _ in range(n):
// 	ai,bi=map(int,input().split(' '))
// 	a.append(ai)
// 	b.append(bi)
// 
// dptable=[1 for i in range(n+1)]
// dptable[0]=0
// a.insert(0,-1*sys.maxsize)
// b.insert(0,0)
// ab=zip(a,b)
// sorted(ab)
// b=[x for _,x in sorted(zip(a,b))]
// a.sort()
// #print(a,"\n",b)
// for i in range(1,len(dptable)):
// 	delupto=a[i]-b[i]
// 	delupto=bisect.bisect_left(a,delupto)
// 	#print(delupto,i)
// 	dptable[i]=dptable[delupto-1]+1
// print(n-max(dptable))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
