// 1203_F1. Complete the Projects (easy version)  (problem 2128, solution 2128_34)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,r=map(int,input().split())
// a=[list(map(int,input().split())) for i in range(n)]
// pos = []
// neg = []
// ans=0
// for x in a:
// 	if x[1]>0:
// 		pos.append(x)
// 	else:
// 		neg.append(x)
// pos.sort(key=lambda k: k[0])
// flag=True
// for x in pos:
// 	if r>=x[0]:
// 		r+=x[1]
// 		ans+=1
// 
// neg.sort(key=lambda i: i[0]+i[1],reverse=True)
// arr=[0]*(r+1)
// for i in range(len(neg)):
// 	for j in range(neg[i][0],r+1):
// 		if j+neg[i][1]>=0:
// 			arr[j+neg[i][1]]=max(arr[j+neg[i][1]],arr[j]+1)
// ans+=max(arr)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, data_list: seq<seq<int>>) returns (output: string)
  requires m >= 0
  requires forall k :: 0 <= k < |data_list| ==> |data_list[k]| >= 2
{
  var pos: seq<(int,int)> := [];
  var neg: seq<(int,int)> := [];
  var idx := 0;
  while idx < |data_list|
    invariant 0 <= idx <= |data_list|
  {
    var xi := data_list[idx];
    if xi[1] > 0 {
      pos := pos + [(xi[0], xi[1])];
    } else {
      neg := neg + [(xi[0], xi[1])];
    }
    idx := idx + 1;
  }
  pos := Sort(pos, (p: (int,int), q: (int,int)) => p.0 < q.0);
  var r := m;
  var ans := 0;
  var pi := 0;
  while pi < |pos|
    invariant 0 <= pi <= |pos|
    invariant r >= 0
  {
    if r >= pos[pi].0 {
      r := if r + pos[pi].1 >= 0 then r + pos[pi].1 else 0;
      ans := ans + 1;
    }
    pi := pi + 1;
  }
  neg := Sort(neg, (p: (int,int), q: (int,int)) => p.0 + p.1 > q.0 + q.1);
  var arr := new int[r+1](kk => 0);
  var ni := 0;
  while ni < |neg|
    invariant 0 <= ni <= |neg|
  {
    var j := neg[ni].0;
    while j <= r
    {
      if 0 <= j <= r && j + neg[ni].1 >= 0 {
        var target := j + neg[ni].1;
        if target <= r {
          var cand := arr[j] + 1;
          if cand > arr[target] {
            arr[target] := cand;
          }
        }
      }
      j := j + 1;
    }
    ni := ni + 1;
  }
  var best := arr[0];
  var bi := 1;
  while bi < arr.Length
  {
    if arr[bi] > best { best := arr[bi]; }
    bi := bi + 1;
  }
  ans := ans + best;
  output := IntToString(ans) + "\n";
}
