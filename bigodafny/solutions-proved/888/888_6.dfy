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

// Amortized two-pointer, same shape as the sibling proof in
// solutions-proved/888/888_179.dfy: the inner loop only ever advances p, and
// every completed outer-loop body advances q by exactly 1 (the sole
// exception -- the pass where the inner loop drives p to twoN -- is the last
// one, per the header comment already in this row). So charge every step
// against the increase of p+q, which is bounded by 2*twoN = 4*n.
method Solve(n: int, m: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 0
  ensures steps <= 60 * n + |output| + 50
{
  steps := 1;
  var doubled := a_list + a_list;
  steps := steps + n + 1;
  var D := ReverseSeq(doubled);
  steps := steps + |doubled| + 1;
  var twoN := 2 * n;
  var Ans: seq<int> := [];
  var t := 0;
  ghost var baseAns := steps;
  while t < |D|
    invariant 0 <= t <= |D|
    invariant |Ans| == t
    invariant steps <= baseAns + 3 * t
    decreases |D| - t
  {
    var v := D[t];
    Ans := Ans + [v * (v + 1) / 2];
    t := t + 1;
    steps := steps + 3;
  }
  assert |D| == 2 * n;
  assert steps <= baseAns + 3 * (2 * n);
  var d := 0;
  var p := 0;
  var q := 0;
  var tot := 0;
  var ans := 0;
  ghost var base1 := steps;
  // doneWaste marks the single outer pass, if any, where the inner loop
  // drives p to twoN with q still short of it: neither `p == q` nor the
  // `elif` fire, q does not advance, and (per the header comment) that pass
  // is necessarily the last, since p == twoN falsifies the outer guard on
  // the very next check. One such pass can happen; the invariant carries 5
  // extra steps of slack to cover it, gated behind p == twoN so it can never
  // be spent twice.
  ghost var doneWaste := false;
  while p < twoN && q < twoN
    invariant 0 <= p <= twoN && 0 <= q <= twoN
    invariant |D| == twoN && |Ans| == twoN
    invariant doneWaste ==> p == twoN
    invariant !doneWaste ==> steps <= base1 + 10 * (p + q) + 20
    invariant doneWaste ==> steps <= base1 + 10 * (p + q) + 25
    decreases twoN - q, twoN - p
  {
    ghost var innerBase := steps;
    ghost var pStart := p;
    while p < twoN && q < twoN && d + D[p] < m
      invariant 0 <= pStart <= p <= twoN
      invariant steps <= innerBase + 10 * (p - pStart)
      decreases twoN - p
    {
      d := d + D[p];
      tot := tot + Ans[p];
      p := p + 1;
      steps := steps + 10;
    }
    if p == q {
      var k := D[p] - m + d;
      tot := tot + Ans[p] - k * (k + 1) / 2;
      if tot > ans { ans := tot; }
      d := 0;
      tot := 0;
      p := p + 1;
      q := q + 1;
      steps := steps + 20;
    } else if p < twoN && q < twoN {
      var k := D[p] - m + d;
      tot := tot + Ans[p] - k * (k + 1) / 2;
      if tot > ans { ans := tot; }
      var minv := if D[q] < d then D[q] else d;
      d := d - minv;
      tot := tot - Ans[q];
      tot := tot - (Ans[p] - k * (k + 1) / 2);
      q := q + 1;
      steps := steps + 10;
    } else {
      assert p == twoN;
      doneWaste := true;
      steps := steps + 5;
    }
  }
  assert p <= twoN && q <= twoN;
  assert steps <= base1 + 10 * (twoN + twoN) + 25;
  output := IntToString(ans) + "\n";
  steps := steps + |output| + 2;
}

function ReverseSeq(s: seq<int>): seq<int>
  ensures |ReverseSeq(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseSeq(s[1..]) + [s[0]]
}
