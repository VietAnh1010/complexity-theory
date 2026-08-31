// 879_A. Borya's Diagnosis  (problem 827, solution 827_40)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # n=int(input())
// # n,k=map(int,input().split())
// # arr=list(map(int,input().split()))
// #ls=list(map(int,input().split()))
// #for i in range(m):
// # for _ in range(int(input())):
// #from collections import Counter
// #from fractions import Fraction
// #s=iter(input())
// from collections import deque
// import math
// ls=[]
// for i in range(int(input())):
//     n,k=map(int,input().split())
//     ls.append((n,k))
// #ls.sort()
// t=ls[0][0]
// c=0
// for i in range(1,len(ls)):
//     var=ls[i][0]
//     if var<=t:
//         c=math.ceil((t-ls[i][0])/ls[i][1])
//         if (t-ls[i][0])%ls[i][1]==0:
//             c+=1
//         #print("c",c)
//         t=ls[i][0]+ls[i][1]*c
//     else:
//         t=ls[i][0]
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
{
  var t := pairs[0].0;
  var idx := 1;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var v := pairs[idx].0;
    var k := pairs[idx].1;
    if v <= t {
      var a := t - v;
      var c := a / k + 1;
      t := v + k * c;
    } else {
      t := v;
    }
    idx := idx + 1;
  }
  output := IntToString(t) + "\n";
}
