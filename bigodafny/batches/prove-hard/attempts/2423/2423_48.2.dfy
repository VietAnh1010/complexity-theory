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
  ensures steps <= 2 * NLogN(|pairs|) + 10 * |pairs| + 21 * MaxFst(pairs) + 49 + |output|
{
  steps := 0;
  steps := steps + SortCost(|pairs|);
  var d := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  SortKeepsElems(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  assert d[|d| - 1] in d;
  MaxFstBound(pairs, d[|d| - 1]);
  SortCostWithin(|pairs|, |pairs|);
  var cur := 0;
  var nex := 0;
  var idx := 0;
  var r := 0;
  steps := steps + 5;
  var limit := d[|d| - 1].0 + 2;
  var i := 0;
  while i < limit
    invariant 0 <= idx <= (if n > 0 then n else 0)
    invariant |d| == |pairs|
    invariant i <= limit <= MaxFst(pairs) + 2
    invariant 0 <= i
    invariant steps <= SortCost(|pairs|) + 5 + 21 * i + 10 * idx
    decreases limit - i
  {
    steps := steps + 2;
    nex := 0;
    var p := k;
    while idx < n && d[idx].0 < i
      invariant 0 <= idx <= (if n > 0 then n else 0)
      invariant steps <= SortCost(|pairs|) + 5 + 21 * i + 2 + 10 * idx
      decreases n - idx
    {
      steps := steps + (3 + if idx < n then 3 else 0);
      steps := steps + 1;
      idx := idx + 1;
    }
    steps := steps + (2 + if idx < n then 3 else 0);
    while idx < n && d[idx].0 == i
      invariant 0 <= idx <= (if n > 0 then n else 0)
      invariant steps <= SortCost(|pairs|) + 5 + 21 * i + 7 + 10 * idx
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
  output := IntToString(r);
  IntToStringDigits(r);
}

import opened Prelude

ghost function MaxFst(s: seq<(int, int)>): int
{
  if |s| == 0 then 0
  else if s[0].0 > MaxFst(s[1..]) then s[0].0 else MaxFst(s[1..])
}

lemma MaxFstBound(s: seq<(int, int)>, x: (int, int))
  requires x in s
  ensures x.0 <= MaxFst(s)
  decreases |s|
{
  if s[0] != x { assert x in s[1..]; MaxFstBound(s[1..], x); }
}
