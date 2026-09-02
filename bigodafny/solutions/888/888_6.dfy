// 1358_D. The Best Vacation  (problem 888, solution 888_6)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x=map(int,input().split());D=list(map(int,input().split()));Ans=[];D+=D;D=D[::-1];d=0;p=0;q=0;tot=0;ans=0
// for i in D:Ans.append(i*(i+1)//2)
// while p<2*n and q<2*n:
//     while p<2*n and q<2*n and d+D[p]<x:d+=D[p];tot+=Ans[p];p+=1
//     if p==q:k=D[p]-x+d;tot+=Ans[p]-k*(k+1)//2;ans=max(ans,tot);d=0;tot=0;p+=1;q+=1    
//     elif p<2*n and q<2*n:k=D[p]-x+d;tot+=Ans[p]-k*(k+1)//2;ans=max(ans,tot);d-=min(D[q],d);tot-=Ans[q];tot-=Ans[p]-k*(k+1)//2;q+=1
// print(ans)          
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string)
{
  var doubled := a_list + a_list;
  var D := ReverseSeq(doubled);
  var twoN := 2 * n;
  var Ans: seq<int> := [];
  var t := 0;
  while t < |D|
    decreases |D| - t
  {
    var v := D[t];
    Ans := Ans + [v * (v + 1) / 2];
    t := t + 1;
  }
  var d := 0;
  var p := 0;
  var q := 0;
  var tot := 0;
  var ans := 0;
  while p < twoN && q < twoN
    decreases twoN - q
  {
    while p < twoN && q < twoN && d + D[p] < m
      decreases twoN - p
    {
      d := d + D[p];
      tot := tot + Ans[p];
      p := p + 1;
    }
    if p == q {
      var k := D[p] - m + d;
      tot := tot + Ans[p] - k * (k + 1) / 2;
      if tot > ans { ans := tot; }
      d := 0;
      tot := 0;
      p := p + 1;
      q := q + 1;
    } else if p < twoN && q < twoN {
      var k := D[p] - m + d;
      tot := tot + Ans[p] - k * (k + 1) / 2;
      if tot > ans { ans := tot; }
      var minv := if D[q] < d then D[q] else d;
      d := d - minv;
      tot := tot - Ans[q];
      tot := tot - (Ans[p] - k * (k + 1) / 2);
      q := q + 1;
    }
  }
  output := IntToString(ans) + "\n";
}

function ReverseSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else ReverseSeq(s[1..]) + [s[0]]
}
