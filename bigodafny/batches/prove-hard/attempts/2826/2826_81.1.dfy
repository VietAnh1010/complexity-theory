// --- Python ---------------------------------------------------------
// import sys,bisect
// n=int(input())
// a,b=[],[]
// for _ in range(n):
// 	ai,bi=map(int,input().split(' '))
// 	a.append(ai)
// 	b.append(bi)
// 
// dptable=[1 for i in range(n+1)]
// dptable[0]=0
// a.insert(0,-1*sys.maxsize)
// b.insert(0,0)
// ab=zip(a,b)
// sorted(ab)
// b=[x for _,x in sorted(zip(a,b))]
// a.sort()
// #print(a,"\n",b)
// for i in range(1,len(dptable)):
// 	delupto=a[i]-b[i]
// 	delupto=bisect.bisect_left(a,delupto)
// 	#print(delupto,i)
// 	dptable[i]=dptable[delupto-1]+1
// print(n-max(dptable))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method BisectLeft(arr: seq<int>, lo0: int, hi0: int, v: int)
    returns (r: int, ghost steps: nat)
  requires 0 <= lo0 <= hi0 <= |arr|
  ensures steps <= 7 * SearchPot(hi0 - lo0) + 1
{
  steps := 0;
  ghost var it: nat := 0;
  var lo := lo0;
  var hi := hi0;
  while lo < hi
    invariant lo0 <= lo <= hi <= hi0
    invariant it + SearchPot(hi - lo) <= SearchPot(hi0 - lo0)
    invariant steps <= 7 * it
    decreases hi - lo
  {
    ghost var kk := hi - lo;
    steps := steps + 2;
    steps := steps + 2;
    var mid := (lo + hi) / 2;
    steps := steps + 2;
    if arr[mid] < v {
      steps := steps + 1;
      lo := mid + 1;
    } else {
      hi := mid;
    }
    BisectStep(kk, hi - lo);
    it := it + 1;
  }
  steps := steps + 1;
  r := lo;
}

method Solve(n: int, pairs: seq<seq<int>>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 10 * NLogN((if n > 0 then n else 0) + 1) + 70 * ((if n > 0 then n else 0) + 1) + |output|
{
  steps := 0;
  steps := steps + 2;
  var nn := if n > 0 then n else 0;
  steps := steps + 1;
  var m := nn + 1;
  steps := steps + 2 * nn;
  var pairArr: seq<(int, int)> := seq(nn, _ /* _v0 */ => (0, 0));
  var i := 0;
  ghost var base1 := steps;
  while i < nn && i < |pairs|
    invariant 0 <= i <= nn
    invariant |pairArr| == nn
    invariant steps <= base1 + 13 * i
  {
    steps := steps + (3 + if i < nn then 2 else 0);
    steps := steps + 1;
    var row := pairs[i];
    steps := steps + 2;
    if |row| >= 2 {
      steps := steps + 4;
      pairArr := pairArr[i := (row[0], row[1])];
    } else {
      steps := steps + 2;
      pairArr := pairArr[i := (0, 0)];
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + (2 + if i < nn then 2 else 0);
  var raw := pairArr;
  steps := steps + SortCost(|raw|);
  var srt := Sort(raw, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  SortCostWithin(|raw|, nn + 1);
  var BIG := -1000000000000000000;
  steps := steps + m;
  var aArr := seq(m, _ /* _v1 */ => 0);
  steps := steps + m;
  var bArr := seq(m, _ /* _v2 */ => 0);
  steps := steps + 1;
  aArr := aArr[0 := BIG];
  steps := steps + 1;
  bArr := bArr[0 := 0];
  var j := 0;
  ghost var base2 := steps;
  while j < nn && j < |srt|
    invariant 0 <= j <= nn
    invariant j <= m - 1
    invariant |aArr| == m && |bArr| == m
    invariant steps <= base2 + 14 * j
  {
    steps := steps + (3 + if j < nn then 2 else 0);
    steps := steps + 4;
    aArr := aArr[j + 1 := srt[j].0];
    steps := steps + 4;
    bArr := bArr[j + 1 := srt[j].1];
    steps := steps + 1;
    j := j + 1;
  }
  steps := steps + (2 + if j < nn then 2 else 0);
  steps := steps + m;
  var dptable := seq(m, _ /* _v3 */ => 1);
  steps := steps + 1;
  dptable := dptable[0 := 0];
  var k := 1;
  ghost var t: nat := 0;
  ghost var K: nat := 7 * SearchPot(m) + 16;
  ghost var base3 := steps;
  while k < m
    invariant 1 <= k <= m
    invariant |aArr| == m && |bArr| == m && |dptable| == m
    invariant t == k - 1
    invariant steps <= base3 + t * K
  {
    steps := steps + 2;
    steps := steps + 3;
    var delupto := aArr[k] - bArr[k];
    var idx, s0 := BisectLeft(aArr, 0, m, delupto);
    steps := steps + s0;
    steps := steps + 1;
    var prevIdx := idx - 1;
    steps := steps + 1;
    if prevIdx < 0 {
      steps := steps + 1;
      prevIdx := m + prevIdx;
    }
    steps := steps + 3;
    if 0 <= prevIdx < m {
      steps := steps + 3;
      dptable := dptable[k := dptable[prevIdx] + 1];
    } else {
      steps := steps + 1;
      dptable := dptable[k := 1];
    }
    steps := steps + 1;
    k := k + 1;
    CostMulDistrib(t, 1, t + 1, K);
    t := t + 1;
  }
  SearchLoopWithin(nn, m, nn + 1, 7, 16);
  assert t == nn;
  steps := steps + 1;
  steps := steps + 1;
  var best := dptable[0];
  var p := 1;
  ghost var base4 := steps;
  while p < m
    invariant 0 <= p <= m
    invariant |dptable| == m
    invariant steps <= base4 + 6 * p
  {
    steps := steps + 2;
    steps := steps + 2;
    if dptable[p] > best {
      steps := steps + 1;
      best := dptable[p];
    }
    steps := steps + 1;
    p := p + 1;
  }
  steps := steps + 1;
  steps := steps + (1 + Digits(n - best));
  output := IntToString(n - best);
  IntToStringDigits(n - best);
}

import opened Prelude
