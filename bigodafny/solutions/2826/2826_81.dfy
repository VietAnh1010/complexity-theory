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

include "../../prelude.dfy"
import opened Prelude

method BisectLeft(arr: array<int>, lo0: int, hi0: int, v: int) returns (r: int)
  requires 0 <= lo0 <= hi0 <= arr.Length
{
  var lo := lo0;
  var hi := hi0;
  while lo < hi
    invariant lo0 <= lo <= hi <= hi0
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if arr[mid] < v {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  r := lo;
}

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  var nn := if n > 0 then n else 0;
  var m := nn + 1;
  var pairArr := new (int, int)[nn];
  var i := 0;
  while i < nn && i < |pairs|
    invariant 0 <= i <= nn
  {
    var row := pairs[i];
    if |row| >= 2 {
      pairArr[i] := (row[0], row[1]);
    } else {
      pairArr[i] := (0, 0);
    }
    i := i + 1;
  }
  var raw := pairArr[..];
  var srt := Sort(raw, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));

  var BIG := -1000000000000000000;
  var aArr := new int[m];
  var bArr := new int[m];
  aArr[0] := BIG;
  bArr[0] := 0;
  var j := 0;
  while j < nn && j < |srt|
    invariant 0 <= j <= nn
    invariant j <= m - 1
  {
    aArr[j+1] := srt[j].0;
    bArr[j+1] := srt[j].1;
    j := j + 1;
  }

  var dptable := new int[m];
  var fillIdx := 0;
  while fillIdx < m
    invariant 0 <= fillIdx <= m
  {
    dptable[fillIdx] := 1;
    fillIdx := fillIdx + 1;
  }
  dptable[0] := 0;
  var k := 1;
  while k < m
    invariant 1 <= k <= m
  {
    var delupto := aArr[k] - bArr[k];
    var idx := BisectLeft(aArr, 0, m, delupto);
    var prevIdx := idx - 1;
    if prevIdx < 0 { prevIdx := m + prevIdx; }
    if 0 <= prevIdx < m {
      dptable[k] := dptable[prevIdx] + 1;
    } else {
      dptable[k] := 1;
    }
    k := k + 1;
  }

  var best := dptable[0];
  var p := 1;
  while p < m
    invariant 0 <= p <= m
  {
    if dptable[p] > best { best := dptable[p]; }
    p := p + 1;
  }
  output := IntToString(n - best);
}
