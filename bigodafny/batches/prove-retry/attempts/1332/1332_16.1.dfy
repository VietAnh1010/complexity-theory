// 1005_E1. Median on Segments (Permutations Edition)  (problem 1332, solution 1332_16)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// class BIT():
//     def __init__(self,n):
//         self.BIT=[0]*(n+1)
//         self.num=n
// 
//     def query(self,idx):
//         res_sum = 0
//         while idx > 0:
//             res_sum += self.BIT[idx]
//             idx -= idx&(-idx)
//         return res_sum
// 
//     #Ai += x O(logN)
//     def update(self,idx,x):
//         while idx <= self.num:
//             self.BIT[idx] += x
//             idx += idx&(-idx)
//         return
// 
// n,m = map(int,input().split())
// a = list(map(int,input().split()))
// 
// def solve(x):
//     tmp = [0 for i in range(n)]
//     for i in range(n):
//         if a[i]>x:
//             tmp[i] = -1
//         else:
//             tmp[i] = 1
//         tmp[i] += tmp[i-1]
// 
//     tmp = [0] + tmp
//     val = list(set([tmp[j] for j in range(n+1)]))
//     val.sort()
//     comp = {i:e+1 for e,i in enumerate(val)}
// 
//     bit = BIT(n+1)
//     res = 0
//     for i in range(n+1):
//         res += bit.query(comp[tmp[i]])
//         bit.update(comp[tmp[i]],1)
//     return res
// 
// print(solve(m) - solve(m-1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Python's x & -x: two's complement on bv64, one operation
function Lowbit(x: int): int
  requires 0 < x < 0x1_0000_0000_0000_0000
  ensures 0 < Lowbit(x) <= x
{
  LowbitBv(x as bv64);
  ((x as bv64) & (0 - (x as bv64))) as int
}

lemma LowbitBv(v: bv64)
  requires v != 0
  ensures 0 < v & (0 - v) <= v
{
}

function DedupSorted(s: seq<int>): seq<int>
  ensures forall v :: v in s <==> v in DedupSorted(s)
  ensures |DedupSorted(s)| <= |s|
  decreases |s|
{
  if |s| == 0 then []
  else if |s| == 1 then [s[0]]
  else if s[0] == s[1] then DedupSorted(s[1..])
  else [s[0]] + DedupSorted(s[1..])
}

lemma MergeMultiset(a: seq<int>, b: seq<int>, less: (int, int) -> bool)
  ensures multiset(Merge(a, b, less)) == multiset(a) + multiset(b)
  decreases |a| + |b|
{
  if |a| == 0 {
  } else if |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeMultiset(a, b[1..], less);
    assert b == [b[0]] + b[1..];
  } else {
    MergeMultiset(a[1..], b, less);
    assert a == [a[0]] + a[1..];
  }
}

lemma SortMultiset(s: seq<int>, less: (int, int) -> bool)
  ensures multiset(Sort(s, less)) == multiset(s)
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortMultiset(s[..|s| / 2], less);
    SortMultiset(s[|s| / 2..], less);
    MergeMultiset(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
    assert s == s[..|s| / 2] + s[|s| / 2..];
  }
}

lemma SortIntsElems(s: seq<int>)
  ensures forall v :: v in s <==> v in SortInts(s)
{
  assert SortInts(s) == Sort(s, (x, y) => x < y);
  SortMultiset(s, (x, y) => x < y);
  assert multiset(SortInts(s)) == multiset(s);
  assert forall v :: v in s <==> v in multiset(s);
  assert forall v :: v in SortInts(s) <==> v in multiset(SortInts(s));
}

ghost function Bx(n: nat): nat
{
  2 * NLogN(n + 1) + (n + 2) * (n + 2) + (n + 1) * (6 * (n + 2) + 12) + 30 * (n + 2) + 10
}

method SolveX(n: int, a: seq<int>, x: int) returns (res: int, ghost steps: nat)
  requires n == |a|
  requires n + 2 < 0x1_0000_0000_0000_0000
  ensures steps <= Bx(n)
{
  steps := 1;
  var tmp2: seq<int> := [0];
  var i := 0;
  var prev := 0;
  ghost var b0 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant |tmp2| == i + 1
    invariant steps == b0 + 6 * i
    decreases n - i
  {
    var cur := if a[i] > x then prev - 1 else prev + 1;
    tmp2 := tmp2 + [cur];
    prev := cur;
    i := i + 1;
    steps := steps + 6;
  }
  var vals := DedupSorted(SortInts(tmp2));
  steps := steps + SortCost(n + 1) + (n + 2) * (n + 2);
  SortCostWithin(n + 1, n + 1);
  SortIntsElems(tmp2);
  assert forall v :: v in tmp2 <==> v in vals;
  var comp: map<int, int> := map[];
  var j := 0;
  ghost var b1 := steps;
  while j < |vals|
    invariant 0 <= j <= |vals|
    invariant comp.Keys == set k | 0 <= k < j :: vals[k]
    invariant forall v :: v in comp ==> 1 <= comp[v] <= j
    invariant steps == b1 + 5 * j
    decreases |vals| - j
  {
    comp := comp[vals[j] := j + 1];
    j := j + 1;
    steps := steps + 5;
  }
  assert comp.Keys == set v | v in vals;
  var bitArr: seq<int> := seq(n + 2, _ => 0);
  steps := steps + n + 3;
  res := 0;
  var t := 0;
  ghost var Kt := 6 * (n + 2) + 12;
  ghost var b2 := steps;
  while t < |tmp2|
    invariant 0 <= t <= |tmp2|
    invariant |tmp2| == n + 1
    invariant |bitArr| == n + 2
    invariant steps <= b2 + t * Kt
    decreases |tmp2| - t
  {
    assert tmp2[t] in tmp2;
    assert tmp2[t] in vals;
    var c := comp[tmp2[t]];
    assert 1 <= c <= |vals| <= |tmp2|;
    steps := steps + 4;
    var qidx := c;
    var sm := 0;
    ghost var b3 := steps;
    while qidx > 0
      invariant 0 <= qidx <= n + 1
      invariant steps + 6 * qidx <= b3 + 6 * c
      decreases qidx
    {
      sm := sm + bitArr[qidx];
      qidx := qidx - Lowbit(qidx);
      steps := steps + 6;
    }
    res := res + sm;
    var uidx := c;
    steps := steps + 2;
    ghost var b4 := steps;
    while uidx <= n + 1
      invariant c <= uidx
      invariant |bitArr| == n + 2
      invariant steps + 6 * (if uidx <= n + 1 then n + 2 - uidx else 0) <= b4 + 6 * (n + 2 - c)
      decreases n + 1 - uidx
    {
      bitArr := bitArr[uidx := bitArr[uidx] + 1];
      uidx := uidx + Lowbit(uidx);
      steps := steps + 6;
    }
    CostMulDistrib(t, 1, t + 1, Kt);
    t := t + 1;
    steps := steps + 2;
  }
  CostMulMonoLeft(t, n + 1, Kt);
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n + 2 < 0x1_0000_0000_0000_0000
  ensures steps <= 2 * Bx(n) + |output| + 10
{
  var r1, s1 := SolveX(n, a_list, k);
  var r2, s2 := SolveX(n, a_list, k - 1);
  output := IntToString(r1 - r2) + "\n";
  IntToStringDigits(r1 - r2);
  steps := 1 + s1 + s2 + 3 + |output|;
}
