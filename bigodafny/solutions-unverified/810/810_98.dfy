// p03388 AtCoder Beginner Contest 093 - Worst Case  (problem 810, solution 810_98)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=int(input())
// def check(t,a,b):
//     k=(2*a+t)//2
//     return k*(2*a+t-k)<a*b
// 
// for i in range(q):
//     a,b=sorted(map(int,input().split()))
//     if a==b or a==b-1:
//         print(2*a-2)
//         continue
//     l,r=1,b-a
//     while l+1<r:
//         t=(l+r)//2
//         if check(t,a,b):
//             l=t
//         else:
//             r=t
//     
//     if check(r,a,b):
//         print(2*a-2+r)
//     elif check(l,a,b):
//         print(2*a-2+l)
//     else:
//         print(2*a-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
{
  output := "";
  var idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
    decreases |pairs| - idx
  {
    var x := pairs[idx][0];
    var y := pairs[idx][1];
    var a := if x < y then x else y;
    var b := if x < y then y else x;
    if a == b || a == b - 1 {
      output := output + IntToString(2 * a - 2) + "\n";
    } else {
      var l := 1;
      var r := b - a;
      while l + 1 < r
        decreases r - l
      {
        var t := (l + r) / 2;
        if Check(t, a, b) {
          l := t;
        } else {
          r := t;
        }
      }
      if Check(r, a, b) {
        output := output + IntToString(2 * a - 2 + r) + "\n";
      } else if Check(l, a, b) {
        output := output + IntToString(2 * a - 2 + l) + "\n";
      } else {
        output := output + IntToString(2 * a - 1) + "\n";
      }
    }
    idx := idx + 1;
  }
}

function Check(t: int, a: int, b: int): bool
{
  var k := (2 * a + t) / 2;
  k * (2 * a + t - k) < a * b
}
