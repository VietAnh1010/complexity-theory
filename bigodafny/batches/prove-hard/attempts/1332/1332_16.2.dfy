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

include "../../../../prelude.dfy"

function Lowbit(x: int): int
  requires 0 < x < 18446744073709551616
  ensures 0 < Lowbit(x) <= x
{
  LowbitBv(x as bv64);
  (x as bv64 & (0 - x as bv64)) as int
}

ghost function Lowbit_steps(x: int): nat
  requires 0 < x < 18446744073709551616
{
  5
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
  if |s| == 0 then
    []
  else if |s| == 1 then
    [s[0]]
  else if s[0] == s[1] then
    DedupSorted(s[1..])
  else
    [s[0]] + DedupSorted(s[1..])
}

ghost function DedupSorted_steps(s: seq<int>): nat
  decreases |s|
{
  3 + if |s| == 0 then 0 else 3 + if |s| == 1 then 2 else 4 + if s[0] == s[1] then 1 + DedupSorted_steps(s[1..]) else 3 + DedupSorted_steps(s[1..]) + |DedupSorted(s[1..])|
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

lemma SqStep(m: nat)
  requires m >= 1
  ensures m * m == (m - 1) * (m - 1) + 2 * m - 1
{
}

lemma DedupBound(s: seq<int>, m: nat)
  requires |s| == m
  ensures DedupSorted_steps(s) <= 3 + 14 * m + m * m
  decreases |s|
{
  if |s| >= 2 {
    DedupBound(s[1..], m - 1);
    SqStep(m);
    assert |DedupSorted(s[1..])| <= m - 1;
  }
}

lemma MulK(m: nat, K: nat)
  requires K == 22 * m + 10
  ensures m * K == 22 * (m * m) + 10 * m
{
  assert m * K == 22 * (m * m) + 10 * m;
}

method SolveX(n: int, a: seq<int>, x: int)
    returns (res: int, ghost steps: nat)
  requires n == |a|
  requires n + 2 < 18446744073709551616
  ensures steps <= 2 * NLogN(n + 1) + 23 * ((n + 1) * (n + 1)) + 45 * (n + 1) + 20
{
  steps := 0;
  steps := steps + 1;
  var tmp2: seq<int> := [0];
  var i := 0;
  var prev := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |tmp2| == i + 1
    invariant steps <= 1 + 9 * i
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + (3 + if a[i] > x then 1 else 1);
    var cur := if a[i] > x then prev - 1 else prev + 1;
    steps := steps + (1 + |[cur]|);
    tmp2 := tmp2 + [cur];
    prev := cur;
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  SortCostWithin(|tmp2|, n + 1);
  DedupBound(SortInts(tmp2), n + 1);
  steps := steps + (SortCost(|tmp2|) + DedupSorted_steps(SortInts(tmp2)));
  var vals := DedupSorted(SortInts(tmp2));
  SortIntsElems(tmp2);
  assert forall v :: v in tmp2 <==> v in vals;
  assert |vals| <= n + 1;
  var comp: map<int, int> := map[];
  ghost var s2 := steps;
  var j := 0;
  while j < |vals|
    invariant steps <= s2 + 7 * j
    invariant 0 <= j <= |vals|
    invariant comp.Keys == set k | 0 <= k < j :: vals[k]
    invariant forall v :: v in comp ==> 1 <= comp[v] <= j
    decreases |vals| - j
  {
    steps := steps + 3;
    steps := steps + 3;
    comp := comp[vals[j] := j + 1];
    steps := steps + 1;
    j := j + 1;
  }
  steps := steps + 2;
  assert comp.Keys == set v | v in vals;
  steps := steps + (1 + (n + 2));
  var bitArr: seq<int> := seq(n + 2, _ /* _v0 */ => 0);
  res := 0;
  ghost var s3 := steps;
  ghost var K := 22 * (n + 1) + 10;
  var t := 0;
  while t < |tmp2|
    invariant 0 <= t <= |tmp2|
    invariant |bitArr| == n + 2
    invariant steps <= s3 + t * K
    decreases |tmp2| - t
  {
    ghost var sb := steps;
    steps := steps + 3;
    assert tmp2[t] in tmp2;
    assert tmp2[t] in vals;
    steps := steps + 2;
    var c := comp[tmp2[t]];
    assert 1 <= c <= |vals| <= |tmp2|;
    var qidx := c;
    var sm := 0;
    ghost var itq: nat := 0;
    ghost var sq := steps;
    while qidx > 0
      invariant 0 <= qidx <= n + 1
      invariant itq + qidx <= c
      invariant steps <= sq + 10 * itq
      decreases qidx
    {
      steps := steps + 2;
      steps := steps + 2;
      sm := sm + bitArr[qidx];
      steps := steps + (1 + Lowbit_steps(qidx));
      qidx := qidx - Lowbit(qidx);
      itq := itq + 1;
    }
    steps := steps + 1;
    steps := steps + 1;
    res := res + sm;
    var uidx := c;
    ghost var itu: nat := 0;
    ghost var su := steps;
    while uidx <= n + 1
      invariant c <= uidx
      invariant |bitArr| == n + 2
      invariant itu + c <= uidx
      invariant itu <= n + 1
      invariant steps <= su + 12 * itu
      decreases n + 1 - uidx
    {
      steps := steps + 3;
      steps := steps + 3;
      bitArr := bitArr[uidx := bitArr[uidx] + 1];
      steps := steps + (1 + Lowbit_steps(uidx));
      uidx := uidx + Lowbit(uidx);
      itu := itu + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    assert steps <= sb + K;
    CostMulDistrib(t, 1, t + 1, K);
    t := t + 1;
  }
  assert t == n + 1;
  MulK(n + 1, K);
  steps := steps + 2;
}

method Solve(n: int, k: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n + 2 < 18446744073709551616
  ensures steps <= 4 * NLogN(n + 1) + 46 * ((n + 1) * (n + 1)) + 90 * (n + 1) + 43 + |output|
{
  steps := 0;
  var r1, s0 := SolveX(n, a_list, k);
  steps := steps + s0;
  steps := steps + 1;
  var r2, s1 := SolveX(n, a_list, k - 1);
  steps := steps + s1;
  steps := steps + (1 + Digits(r1 - r2) + |"\n"|);
  IntToStringDigits(r1 - r2);
  output := IntToString(r1 - r2) + "\n";
}

import opened Prelude
