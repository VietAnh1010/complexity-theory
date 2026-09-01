// 349_A. Cinema Line  (problem 2281, solution 2281_358)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// mod=1000000007
// def power(a,b):
//     res=1
//     b=b%(mod-1)
//     while(b>0):
//         if b%2!=0:
//             res=((res%mod)*(a%mod))%mod
//         b=b//2
//         a=a%mod
//         a=(a*a)%mod
//     res=res%mod
//     return res
// #n=int(input())
// #a=[int(i) for i in input().split()]
// #c=[[0 for x in range(1001)] for y in range(1001)]
// #n,q=[int(i) for i in input().split()]
// #a.sort(reverse=True)
// n=int(input())
// a=[int(i) for i in input().split()]
// a1=0
// b=0
// c=0
// f=1
// for i in range(n):
//     if a[i]==50:
//         if a1>0:
//             a1-=1
//             b+=1
//         else:
//             f=0
//             break
//     elif a[i]==100:
//         if a1>0 and b>0:
//             a1-=1
//             b-=1
//             c+=1
//         elif a1>=3:
//             a1-=3
//             c+=1
//         else:
//             f=0
//             break
//     else:
//         a1+=1
// if f==0:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var a1 := 0;
  var b := 0;
  var c := 0;
  var f := true;
  var i := 0;
  while i < n && f
    decreases n - i
  {
    var v := a_list[i];
    if v == 50 {
      if a1 > 0 {
        a1 := a1 - 1;
        b := b + 1;
      } else {
        f := false;
      }
    } else if v == 100 {
      if a1 > 0 && b > 0 {
        a1 := a1 - 1;
        b := b - 1;
        c := c + 1;
      } else if a1 >= 3 {
        a1 := a1 - 3;
        c := c + 1;
      } else {
        f := false;
      }
    } else {
      a1 := a1 + 1;
    }
    i := i + 1;
  }
  output := if f then "YES" else "NO";
}
