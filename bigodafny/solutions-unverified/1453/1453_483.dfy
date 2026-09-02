// 1197_B. Pillars  (problem 1453, solution 1453_483)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// p=1
// r=1
// e=0
// if r==0:
//     print("NO")
// else:
//     k=max(a)
//     t=a.index(k)
//     c=max(t,n-t-1)
//     for i in range(c):
//         if i<t:
//             if a[i]<a[i+1]:
//                 pass
//             else:
//                 e=1
//                 break
//         if i+t<n-1:
//             if a[i+t]>a[i+1+t]:
//                 pass
//             else:
//                 e=1
//                 break
//     if e==1:
//         print("NO")
//     else:
//         print("YES")
//             
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var k := MaxSeq(a_list);
  var t := 0;
  while a_list[t] != k
    decreases n - t
  {
    t := t + 1;
  }
  var c := if t > n - t - 1 then t else n - t - 1;
  var e := 0;
  var i := 0;
  while i < c && e == 0
    decreases c - i
  {
    if i < t {
      if a_list[i] < a_list[i+1] {
      } else {
        e := 1;
      }
    }
    if e == 0 && i + t < n - 1 {
      if a_list[i+t] > a_list[i+1+t] {
      } else {
        e := 1;
      }
    }
    i := i + 1;
  }
  output := if e == 1 then "NO" else "YES";
}
