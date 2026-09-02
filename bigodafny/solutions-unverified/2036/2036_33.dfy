// 471_A. MUH and Sticks  (problem 2036, solution 2036_33)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// alph="abcdefghijklmnopqrstuvwxyz"
// #-----------------------------------
// 
// l=list(map(int,input().split()))
// l.sort()
// if l[2]!=l[3]:
//     print("Alien")
// else:
//     k=l[2];t=l.count(k)
//     if t>=4:
//         for i in range(4):
//             del(l[l.index(k)])
//         if l[0]==l[1]:
//             print("Elephant")
//         else:
//             print("Bear")
//     else:
//         print("Alien")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(numbers: seq<int>) returns (output: string)
{
  var l := SortInts(numbers);
  if l[2] != l[3] {
    output := "Alien";
  } else {
    var k := l[2];
    var t := 0;
    var idx := 0;
    while idx < |l|
      decreases |l| - idx
    {
      if l[idx] == k { t := t + 1; }
      idx := idx + 1;
    }
    if t >= 4 {
      var newl: seq<int> := [];
      var removed := 0;
      idx := 0;
      while idx < |l|
        decreases |l| - idx
      {
        if l[idx] == k && removed < 4 {
          removed := removed + 1;
        } else {
          newl := newl + [l[idx]];
        }
        idx := idx + 1;
      }
      if newl[0] == newl[1] {
        output := "Elephant";
      } else {
        output := "Bear";
      }
    } else {
      output := "Alien";
    }
  }
}
