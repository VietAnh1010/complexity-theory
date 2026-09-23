// 608_C. Chain Reaction  (problem 2826, solution 2826_81)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

// PROOF NOTE (relation: confirms).
// A sort of the n pairs, then for each of the n positions a bisect over the
// m = n + 1 sorted keys. BisectLeft carries its own step count, bounded by the
// prelude's SearchPot potential; the n searches and the sort fold into
// NLogN(n + 1) by SearchLoopWithin and SortCostWithin.

include "../../prelude.dfy"
import opened Prelude

method BisectLeft(arr: seq<int>, lo0: int, hi0: int, v: int) returns (r: int, ghost steps: nat)
  requires 0 <= lo0 <= hi0 <= |arr|
  ensures steps <= 3 * SearchPot(hi0 - lo0) + 1
{
  var lo := lo0;
  var hi := hi0;
  steps := 1;
  ghost var it: nat := 0;
  while lo < hi
    invariant lo0 <= lo <= hi <= hi0
    invariant it + SearchPot(hi - lo) <= SearchPot(hi0 - lo0)
    invariant steps == 1 + 3 * it
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    ghost var k := hi - lo;
    if arr[mid] < v {
      lo := mid + 1;
    } else {
      hi := mid;
    }
    BisectStep(k, hi - lo);
    it := it + 1;
    steps := steps + 3;
  }
  r := lo;
}

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string, ghost steps: nat)
  ensures var nn := if n > 0 then n else 0;
          steps <= 5 * NLogN(nn + 1) + 20 * nn + 30
{
  var nn := if n > 0 then n else 0;
  var m := nn + 1;
  var pairArr: seq<(int, int)> := seq(nn, _ => (0, 0));
  steps := 1 + nn;
  var i := 0;
  while i < nn && i < |pairs|
    invariant 0 <= i <= nn
    invariant |pairArr| == nn
    invariant steps == 1 + nn + 3 * i
  {
    var row := pairs[i];
    if |row| >= 2 {
      pairArr := pairArr[i := (row[0], row[1])];
    } else {
      pairArr := pairArr[i := (0, 0)];
    }
    i := i + 1;
    steps := steps + 3;
  }
  var raw := pairArr;
  var srt := Sort(raw, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  steps := steps + SortCost(nn);
  SortCostWithin(nn, m);
  ghost var s1 := steps;

  var BIG := -1000000000000000000;
  var aArr := seq(m, _ => 0);
  var bArr := seq(m, _ => 0);
  aArr := aArr[0 := BIG];
  bArr := bArr[0 := 0];
  steps := steps + 2 * m + 2;
  var j := 0;
  while j < nn && j < |srt|
    invariant 0 <= j <= nn
    invariant j <= m - 1
    invariant |aArr| == m && |bArr| == m
    invariant steps == s1 + 2 * m + 2 + 3 * j
  {
    aArr := aArr[j+1 := srt[j].0];
    bArr := bArr[j+1 := srt[j].1];
    j := j + 1;
    steps := steps + 3;
  }

  var dptable := seq(m, _ => 1);
  dptable := dptable[0 := 0];
  steps := steps + m + 1;
  ghost var base := steps;
  ghost var K: nat := 3 * SearchPot(m) + 6;
  var k := 1;
  while k < m
    invariant 1 <= k <= m
    invariant |aArr| == m && |bArr| == m && |dptable| == m
    invariant steps <= base + (k - 1) * K
  {
    var delupto := aArr[k] - bArr[k];
    var idx: int;
    ghost var bs: nat;
    idx, bs := BisectLeft(aArr, 0, m, delupto);
    steps := steps + bs;
    var prevIdx := idx - 1;
    if prevIdx < 0 { prevIdx := m + prevIdx; }
    if 0 <= prevIdx < m {
      dptable := dptable[k := dptable[prevIdx] + 1];
    } else {
      dptable := dptable[k := 1];
    }
    k := k + 1;
    steps := steps + 5;
    CostMulDistrib(k - 2, 1, k - 1, K);
  }
  SearchLoopWithin(m - 1, m, m, 3, 6);
  assert steps <= base + 3 * NLogN(m) + 6 * m;
  ghost var s4 := steps;

  var best := dptable[0];
  var p := 1;
  while p < m
    invariant 1 <= p <= m
    invariant |dptable| == m
    invariant steps == s4 + 2 * (p - 1)
  {
    if dptable[p] > best { best := dptable[p]; }
    p := p + 1;
    steps := steps + 2;
  }
  output := IntToString(n - best);
  steps := steps + 2;
}
