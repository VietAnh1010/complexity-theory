// 24_A. Ring road  (problem 348, solution 348_33)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys,math
// n=int(sys.stdin.readline())
// start =[]
// end=[]
// ans1=0
// ans2=0
// for i in range(n):
//     a,b,c=map(int,sys.stdin.readline().split())
//     if (a in start) or (b in end):
//         ans1+=c
//         start.append(b)
//         end.append(a)
//     else:
//         ans2+=c
//         start.append(a)
//         end.append(b)
// print(min(ans1,ans2))
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt(xs: seq<int>, x: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == x then true
  else ContainsInt(xs[1..], x)
}

// Isolated multiplication: (a+1)*c == a*c + c.
lemma MulDistribAdd(a: int, c: int)
  ensures (a + 1) * c == a * c + c
{}

method Solve(n: int, v_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |v_list| ==> |v_list[k]| >= 3
  ensures steps <= (10 * |v_list| + 10) * |v_list| + 10
{
  steps := 1;
  var start: seq<int> := [];
  var end_: seq<int> := [];
  var ans1 := 0;
  var ans2 := 0;
  var idx := 0;
  ghost var ibase := steps;
  while idx < |v_list|
    invariant 0 <= idx <= |v_list|
    invariant |start| == idx
    invariant |end_| == idx
    invariant steps <= ibase + (10 * |v_list| + 10) * idx
    decreases |v_list| - idx
  {
    var a := v_list[idx][0];
    var b := v_list[idx][1];
    var c := v_list[idx][2];
    steps := steps + 3;
    ghost var csteps1 := |start|;
    ghost var csteps2 := |end_|;
    var contains1 := ContainsInt(start, a);
    var contains2 := ContainsInt(end_, b);
    steps := steps + csteps1 + csteps2;
    if contains1 || contains2 {
      ans1 := ans1 + c;
      start := start + [b];
      end_ := end_ + [a];
      steps := steps + 3;
    } else {
      ans2 := ans2 + c;
      start := start + [a];
      end_ := end_ + [b];
      steps := steps + 3;
    }
    idx := idx + 1;
    steps := steps + 1;
    assert (idx - 1 + 1) * (10 * |v_list| + 10) == (idx - 1) * (10 * |v_list| + 10) + (10 * |v_list| + 10)
      by { MulDistribAdd(idx - 1, 10 * |v_list| + 10); }
  }
  output := IntToString(if ans1 < ans2 then ans1 else ans2);
  steps := steps + 1;
}
