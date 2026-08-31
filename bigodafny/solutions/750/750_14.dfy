// 621_B. Wet Shark and Bishops  (problem 750, solution 750_14)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// n=int(sys.stdin.readline())
// a=[]
// b=[]
// res=0
// for i in range(n):
//     _a, _b = list(map(int, sys.stdin.readline().split()))
//     a.append(_a+_b)
//     b.append(_a-_b)
// 
// a.sort()
// b.sort()
// i=0
// while i<n:
//     cnt=1
//     while i+1<len(a) and a[i]==a[i+1]:
//         cnt+=1
//         i+=1
//     res+=cnt*(cnt-1)//2
//     i+=1
// 
// i=0
// while i<n:
//     cnt=1
//     while i+1<len(b) and b[i]==b[i+1]:
//         cnt+=1
//         i+=1
//     res+=cnt*(cnt-1)//2
//     i+=1
// 
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data_points: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
