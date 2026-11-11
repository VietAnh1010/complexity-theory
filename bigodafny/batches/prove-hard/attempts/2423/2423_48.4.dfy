// --- Python ---------------------------------------------------------
// def a():	
// 	n, v = list(map(int, input().split(" ")))
// 	d = []
// 	for i in range(n):
// 		d.append(list(map(int, input().split(" "))))
// 	d.sort()
// 
// 	cur = 0
// 	nex = 0
// 	k = 0
// 	r = 0
// 	for i in range(d[-1][0] + 2):
// 		nex = 0
// 		p = v
// 		if k != n:
// 			while(d[k][0] < i):
// 				k += 1
// 				if k == n:
// 					break
// 		if k != n:
// 			while(d[k][0] == i):
// 				nex += d[k][1]
// 				k += 1
// 				if k == n:
// 					break
// 		r += min(p, cur)
// 		p -= min(p, cur)
// 		r += min(p, nex)
// 		cur = nex - min(p, nex)
// 	return r
// 
// print(a())
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, k: int, pairs: seq<(int, int)>)
    returns (output: string, ghost steps: nat)
  requires |pairs| >= 1
  requires n <= |pairs|
  ensures steps <= 2 * NLogN(|pairs|) + 11 * (if n > 0 then n else 0) + 23 * (MaxFst(pairs) + 2) + 8 + |output|
{
  steps := 0;
  steps := steps + SortCost(|pairs|);
  var d := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  var cur := 0;
  var nex := 0;
  var idx := 0;
  var r := 0;
  steps := steps + 5;
  var limit := d[|d| - 1].0 + 2;
  ghost var base := steps;
  ghost var nn := if n > 0 then n else 0;
  SortCostWithin(|pairs|, |pairs|);
  SortKeepsElems(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  assert d[|d| - 1] in pairs;
  MaxFstBound(pairs, d[|d| - 1]);
  var i := 0;
  while i < limit
    invariant 0 <= idx
    invariant |d| == |pairs|
    invariant idx <= nn
    invariant 0 <= i <= limit
    invariant steps <= base + 23 * i + 11 * idx
    decreases limit - i
  {
    ghost var s0 := steps;
    ghost var idx0 := idx;
    steps := steps + 2;
    nex := 0;
    var p := k;
    while idx < n && d[idx].0 < i
      invariant 0 <= idx
      invariant idx0 <= idx <= nn
      invariant steps <= s0 + 2 + 8 * (idx - idx0)
      decreases n - idx
    {
      steps := steps + (3 + if idx < n then 3 else 0);
      steps := steps + 1;
      idx := idx + 1;
    }
    steps := steps + (2 + if idx < n then 3 else 0);
    ghost var s1 := steps;
    ghost var idx1 := idx;
    while idx < n && d[idx].0 == i
      invariant 0 <= idx
      invariant idx1 <= idx <= nn
      invariant steps <= s1 + 11 * (idx - idx1)
      decreases n - idx
    {
      steps := steps + (3 + if idx < n then 3 else 0);
      steps := steps + 3;
      nex := nex + d[idx].1;
      steps := steps + 1;
      idx := idx + 1;
    }
    steps := steps + (2 + if idx < n then 3 else 0);
    steps := steps + 2;
    var m1 := if p < cur then p else cur;
    steps := steps + 1;
    r := r + m1;
    steps := steps + 1;
    p := p - m1;
    steps := steps + 2;
    var m2 := if p < nex then p else nex;
    steps := steps + 1;
    r := r + m2;
    steps := steps + 1;
    cur := nex - m2;
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + Digits(r);
  IntToStringDigits(r);
  output := IntToString(r);
}

import opened Prelude

ghost function MaxFst(s: seq<(int, int)>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else
    var m := MaxFst(s[1..]);
    if s[0].0 > m then s[0].0 else m
}

lemma MaxFstBound(s: seq<(int, int)>, x: (int, int))
  requires x in s
  ensures x.0 <= MaxFst(s)
  decreases |s|
{
  if s[0] != x { MaxFstBound(s[1..], x); }
}
