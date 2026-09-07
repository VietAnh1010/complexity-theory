// 1425_H. Huge Boxes of Animal Toys  (problem 1170, solution 1170_10)
// time complexity: O(n*m)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for _ in range(t):
//     l=list(map(int,input().split()))
//     a=[0]*4
//     if(l[0]+l[3]!=0):
//         a[0]=1
//         a[3]=1
//     if(l[1]+l[2]!=0):
//         a[1]=1
//         a[2]=1
//     if((l[1]+l[0])%2==0):
//         a[0]=0
//         a[1]=0
//     else:
//         a[2]=0
//         a[3]=0
//     for x in a:
//         if(x==0):
//             print("Tidak",end=" ")
//         else:
//             print("Ya",end=" ")
//     print(" ")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrices: seq<seq<int>>) returns (output: string)
  requires forall i :: 0 <= i < |matrices| ==> |matrices[i]| >= 4
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |matrices|
    invariant 0 <= i <= |matrices|
    decreases |matrices| - i
  {
    var l := matrices[i];
    var a0 := if l[0] + l[3] != 0 then 1 else 0;
    var a3 := if l[0] + l[3] != 0 then 1 else 0;
    var a1 := if l[1] + l[2] != 0 then 1 else 0;
    var a2 := if l[1] + l[2] != 0 then 1 else 0;
    if (l[1] + l[0]) % 2 == 0 {
      a0 := 0;
      a1 := 0;
    } else {
      a2 := 0;
      a3 := 0;
    }
    var w0 := if a0 == 0 then "Tidak" else "Ya";
    var w1 := if a1 == 0 then "Tidak" else "Ya";
    var w2 := if a2 == 0 then "Tidak" else "Ya";
    var w3 := if a3 == 0 then "Tidak" else "Ya";
    parts := parts + [w0 + " " + w1 + " " + w2 + " " + w3 + "  \n"];
    i := i + 1;
  }
  output := Join(parts, "");
}
