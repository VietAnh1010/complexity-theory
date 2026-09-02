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

method Solve(n: int, v_list: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |v_list| ==> |v_list[k]| >= 3
{
  var start: seq<int> := [];
  var end_: seq<int> := [];
  var ans1 := 0;
  var ans2 := 0;
  var idx := 0;
  while idx < |v_list|
    invariant 0 <= idx <= |v_list|
    decreases |v_list| - idx
  {
    var a := v_list[idx][0];
    var b := v_list[idx][1];
    var c := v_list[idx][2];
    if ContainsInt(start, a) || ContainsInt(end_, b) {
      ans1 := ans1 + c;
      start := start + [b];
      end_ := end_ + [a];
    } else {
      ans2 := ans2 + c;
      start := start + [a];
      end_ := end_ + [b];
    }
    idx := idx + 1;
  }
  output := IntToString(if ans1 < ans2 then ans1 else ans2);
}
