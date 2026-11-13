// 514_B. Han Solo and Lazer Gun  (problem 1027, solution 1027_458)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, x1, y1 = [int(s) for s in input().split()] 
// slope = {}
// shoot=0
// for i in range(n):
//     x2,y2=[int(s) for s in input().split()]
//     if(x2-x1)==0:
//         m="a"
//     else:
//         m = (y2-y1)/(x2-x1)
//     
//     if m not in slope:
//         shoot+=1
//         slope[m] = 0
// print(shoot)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<(int, int)>) returns (output: string, ghost steps: nat)
  ensures steps <= 22 * |d_list| + 6 + |output|
{
  steps := 0;
  var D := 0;
  var t := 0;
  while t < |d_list|
    invariant 0 <= t <= |d_list|
    invariant steps <= 8 * t
    decreases |d_list| - t
  {
    var ax := AbsInt(d_list[t].0 - b);
    if ax > D { D := ax; }
    t := t + 1;
    steps := steps + 8;
  }
  var L := D * D + 1;
  steps := steps + 2;
  var slope: map<(bool, int), int> := map[];
  var shoot := 0;
  var i := 0;
  while i < |d_list|
    invariant 0 <= i <= |d_list|
    invariant steps <= 8 * |d_list| + 2 + 14 * i
    decreases |d_list| - i
  {
    var dx := d_list[i].0 - b;
    var dy := d_list[i].1 - c;
    var m: (bool, int);
    if dx == 0 {
      m := (true, 0);
    } else {
      m := (false, FloorDiv(dy * L, dx));
    }
    if m !in slope {
      shoot := shoot + 1;
      slope := slope[m := 0];
    }
    i := i + 1;
    steps := steps + 14;
  }
  output := IntToString(shoot);
  IntToStringDigits(shoot);
  steps := steps + Digits(shoot);
}
