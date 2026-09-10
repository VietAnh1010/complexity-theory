// 1332_16 (problem 1332) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : 2 * SolveXBound(n) + ResBound(n) + 7
//   proved class    : O(n+m)
//   agent verdict   : gave_up
//   reference label : O(nlogn)
//   prediction correct against the label: False
//   all gates passed: False
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     tmp2 built via seq append (tmp2+[cur]) each costing |tmp2|; that alone
//     is quadratic in n=|a_list|, per GUIDE's append trap
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1332_16
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
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
//     # [complexity note redacted for this experiment]
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
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Lowbit(x: int): int
  requires x > 0
  ensures 0 < Lowbit(x) <= x
  decreases x
{
  if x % 2 != 0 then 1 else 2 * Lowbit(x / 2)
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

// ---- ghost cost model -----------------------------------------------------
// Every seq append / functional update here is charged its real cost: the
// length of the sequence being copied. That length is always <= n+2, so a
// flat charge of (n+2) per such operation is a safe (if loose) upper bound.

ghost function LinCost(s: seq<int>, c: nat): nat
  decreases |s|
{
  if |s| <= 1 then 1 else LinCost(s[1..], c) + c
}

lemma LinCostExact(s: seq<int>, c: nat)
  requires |s| >= 1
  ensures LinCost(s, c) == 1 + (|s| - 1) * c
  decreases |s|
{
  if |s| == 1 {
  } else {
    LinCostExact(s[1..], c);
  }
}

ghost function MergeCost(s: seq<int>, c: nat): nat
  decreases |s|
{
  if |s| <= 1 then 1 else MergeCost(s[..|s| / 2], c) + MergeCost(s[|s| / 2..], c) + c
}

lemma MergeCostExact(s: seq<int>, c: nat)
  requires |s| >= 1
  ensures MergeCost(s, c) == (|s| - 1) * c + |s|
  decreases |s|
{
  if |s| == 1 {
  } else {
    MergeCostExact(s[..|s| / 2], c);
    MergeCostExact(s[|s| / 2..], c);
  }
}

ghost function PerTBound(n: int): nat
  requires n >= 0
{
  (n + 2) + (2 * n + 3) * (n + 3) + 5
}

lemma MulMonoRightNat(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{}

lemma IntToStringDigitBound(x: int)
  requires x >= 0
  ensures IntToStringCost(x) <= x + 2
  decreases x
{
  if x < 10 {
  } else {
    IntToStringDigitBound(x / 10);
  }
}

ghost function IntToStringCost(x: int): nat
  decreases if x < 0 then 1 - x else x
{
  if x < 0 then 1 + IntToStringCost(-x)
  else if x < 10 then 1
  else 1 + IntToStringCost(x / 10)
}

lemma IntToStringCostUniversal(x: int)
  ensures IntToStringCost(x) <= (if x < 0 then -x else x) + 3
{
  if x < 0 {
    IntToStringDigitBound(-x);
  } else {
    IntToStringDigitBound(x);
  }
}

method SolveX(n: int, a: seq<int>, x: int) returns (res: int, ghost steps: nat)
  requires n == |a|
  requires n >= 0
  ensures steps <= 1 + n * (n + 3) + (n * (n + 3) + (n + 1)) + (1 + n * (n + 3))
                  + (n + 1) * (n + 3) + (n + 1) * PerTBound(n)
{
  steps := 1;
  var tmp2: seq<int> := [0];
  var i := 0;
  var prev := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |tmp2| == i + 1
    invariant steps <= 1 + i * (n + 3)
    decreases n - i
  {
    var cur := if a[i] > x then prev - 1 else prev + 1;
    tmp2 := tmp2 + [cur];
    prev := cur;
    i := i + 1;
    steps := steps + (n + 3);
  }
  assert |tmp2| == n + 1;
  var sortedTmp := SortInts(tmp2);
  var vals := DedupSorted(sortedTmp);
  MergeCostExact(tmp2, n + 3);
  assert |sortedTmp| == n + 1;
  LinCostExact(sortedTmp, n + 3);
  steps := steps + MergeCost(tmp2, n + 3);
  steps := steps + LinCost(sortedTmp, n + 3);
  SortIntsElems(tmp2);
  assert forall v :: v in tmp2 <==> v in vals;
  var comp: map<int, int> := map[];
  var j := 0;
  ghost var stepsBeforeComp := steps;
  while j < |vals|
    invariant 0 <= j <= |vals|
    invariant comp.Keys == set k | 0 <= k < j :: vals[k]
    invariant forall v :: v in comp ==> 1 <= comp[v] <= j
    invariant steps <= stepsBeforeComp + j * (n + 3)
    decreases |vals| - j
  {
    comp := comp[vals[j] := j + 1];
    j := j + 1;
    steps := steps + (n + 3);
  }
  assert comp.Keys == set v | v in vals;
  assert |vals| <= |tmp2| == n + 1;
  MulMonoRightNat(n + 3, |vals|, n + 1);
  var bitArr: seq<int> := seq(n + 2, _ => 0);
  res := 0;
  var t := 0;
  ghost var touchCount: nat := 0;
  ghost var stepsBeforeBit := steps;
  while t < |tmp2|
    invariant 0 <= t <= |tmp2|
    invariant |bitArr| == n + 2
    invariant forall idx :: 0 <= idx < |bitArr| ==> bitArr[idx] <= touchCount
    invariant touchCount <= t * (2 * n + 4)
    invariant 0 <= res <= t * ((n + 2) * (t * (2 * n + 4)))
    invariant steps <= stepsBeforeBit + t * PerTBound(n)
    decreases |tmp2| - t
  {
    assert tmp2[t] in tmp2;
    assert tmp2[t] in vals;
    var c := comp[tmp2[t]];
    assert 1 <= c <= |vals| <= |tmp2|;
    var qidx := c;
    var sm := 0;
    ghost var stepsQStart := steps;
    ghost var tc0 := touchCount;
    while qidx > 0
      invariant 0 <= qidx <= n + 1
      invariant 0 <= sm <= (c - qidx) * tc0
      invariant steps <= stepsQStart + (c - qidx)
      decreases qidx
    {
      sm := sm + bitArr[qidx];
      qidx := qidx - Lowbit(qidx);
      steps := steps + 1;
    }
    MulMonoRightNat(tc0, c, n + 2);
    assert sm <= (n + 2) * tc0;
    res := res + sm;
    var uidx := c;
    ghost var stepsUStart := steps;
    while uidx <= n + 1
      invariant c <= uidx
      invariant |bitArr| == n + 2
      invariant forall idx :: 0 <= idx < |bitArr| ==> bitArr[idx] <= touchCount
      invariant touchCount <= tc0 + (uidx - c)
      invariant steps <= stepsUStart + (uidx - c) * (n + 3)
      decreases n + 1 - uidx
    {
      bitArr := bitArr[uidx := bitArr[uidx] + 1];
      uidx := uidx + Lowbit(uidx);
      touchCount := touchCount + 1;
      steps := steps + (n + 3);
    }
    assert uidx > n + 1;
    assert uidx <= (n + 1) + Lowbit(n + 1);
    assert uidx - c <= 2 * n + 3;
    assert touchCount <= tc0 + (2 * n + 3);
    assert touchCount <= (t + 1) * (2 * n + 4);
    steps := steps + 5;
    t := t + 1;
  }
}

ghost function SolveXBound(n: int): nat
  requires n >= 0
{
  1 + n * (n + 3) + (n * (n + 3) + (n + 1)) + (1 + n * (n + 3))
    + (n + 1) * (n + 3) + (n + 1) * PerTBound(n)
}

ghost function ResBound(n: int): nat
  requires n >= 0
{
  (n + 1) * (n + 2) * (n + 2)
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 0
  ensures steps <= 2 * SolveXBound(n) + ResBound(n) + 7
{
  var r1, s1 := SolveX(n, a_list, k);
  var r2, s2 := SolveX(n, a_list, k - 1);
  IntToStringCostUniversal(r1 - r2);
  steps := s1 + s2 + IntToStringCost(r1 - r2) + 4;
  output := IntToString(r1 - r2) + "\n";
}
