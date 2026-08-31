// 440_A. Forgotten Episode  (problem 2742, solution 2742_0)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input=sys.stdin.buffer.readline
// 
// n=int(input())
// arr=list(map(int,input().split()))
// arr.sort()
// z=0
// for i in range(0,n-1):
// 	if arr[i]==i+1:
// 		continue
// 	else:
// 		print(i+1)
// 		z=1
// 		break
// if z==0:
// 	print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
