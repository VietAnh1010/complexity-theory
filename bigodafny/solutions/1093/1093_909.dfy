// 25_A. IQ test  (problem 1093, solution 1093_909)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #t=int(input())
// #for i in range(t):
// #    n,r=map(int,input().split())
// #    a=list(map(int,input().split()))
// #    bomb=0
// #    a.sort()
// #    a=list(set(a))
// #    n=len(a)
// #    for i in range(n):
// #        if (a[i]>bomb*r):
// #            bomb+=1
// #    print(bomb-1)
// n=int(input())
// a=list(map(int,input().split()))
// leven,lodd,ceven,codd=0,0,0,0
// for i in range(n):
//     if a[i]%2==0:
//         ceven+=1
//         leven=i
//     else:
//         codd+=1
//         lodd=i
// if codd==1:
//     print(lodd+1)
// else:
//     print(leven+1)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var countEven := 0;
  var countOdd := 0;
  var idxEven := 0;
  var idxOdd := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] % 2 == 0 {
      countEven := countEven + 1;
      idxEven := i;
    } else {
      countOdd := countOdd + 1;
      idxOdd := i;
    }
    i := i + 1;
  }
  var ans := if countEven == 1 then idxEven + 1 else idxOdd + 1;
  output := IntToString(ans);
}

