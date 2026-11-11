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

include "../../../../prelude.dfy"

method Solve(numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires |numbers| == 6
  ensures steps <= 200
{
  steps := 0;
  steps := steps + SortCost(|numbers|);
  assert SortCost(6) == 22 by {
    assert SortCost(1) == 1;
    assert SortCost(2) == 4;
    assert SortCost(3) == 8;
  }
  var l := SortInts(numbers);
  steps := steps + 3;
  if l[2] != l[3] {
    output := "Alien";
  } else {
    steps := steps + 1;
    var k := l[2];
    var t := 0;
    var idx := 0;
    ghost var s1 := steps;
    while idx < |l|
      invariant idx <= |l| && |l| == 6
      invariant steps <= s1 + 7 * idx
      decreases |l| - idx
    {
      steps := steps + 3;
      steps := steps + 2;
      if l[idx] == k {
        steps := steps + 1;
        t := t + 1;
      }
      steps := steps + 1;
      idx := idx + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    if t >= 4 {
      var newl: seq<int> := [];
      var removed := 0;
      idx := 0;
      ghost var s2 := steps;
      while idx < |l|
        invariant idx <= |l| && |l| == 6
        invariant steps <= s2 + 11 * idx
        invariant |newl| + removed == idx
        invariant removed <= 4
        decreases |l| - idx
      {
        steps := steps + 3;
        steps := steps + (3 + if l[idx] == k then 1 else 0);
        if l[idx] == k && removed < 4 {
          steps := steps + 1;
          removed := removed + 1;
        } else {
          steps := steps + (2 + |[l[idx]]|);
          newl := newl + [l[idx]];
        }
        steps := steps + 1;
        idx := idx + 1;
      }
      steps := steps + 2;
      steps := steps + 3;
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

import opened Prelude
