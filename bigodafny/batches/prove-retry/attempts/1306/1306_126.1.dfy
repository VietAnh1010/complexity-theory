// 1011_B. Planning The Expedition  (problem 1306, solution 1306_126)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import*
// R=lambda:map(int,input().split())
// n,m=R()
// a=Counter(R()).values()
// i=1
// while sum(x//i for x in a)>=n:i+=1
// print(i-1)
//           
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountOccur1306(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + CountOccur1306(a[1..], v)
}

function RemoveAll1306(a: seq<int>, v: int): seq<int>
  ensures |RemoveAll1306(a, v)| <= |a|
  decreases |a|
{
  if |a| == 0 then []
  else if a[0] == v then RemoveAll1306(a[1..], v)
  else [a[0]] + RemoveAll1306(a[1..], v)
}

function GroupCounts1306(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else [CountOccur1306(a, a[0])] + GroupCounts1306(RemoveAll1306(a[1..], a[0]))
}

function SumDiv1306(counts: seq<int>, day: int): int
  requires day > 0
  decreases |counts|
{
  if |counts| == 0 then 0
  else counts[0] / day + SumDiv1306(counts[1..], day)
}

lemma CountLe1306(a: seq<int>, v: int)
  ensures 0 <= CountOccur1306(a, v) <= |a|
  decreases |a|
{
  if |a| > 0 { CountLe1306(a[1..], v); }
}

lemma GCtsFacts1306(a: seq<int>)
  ensures |GroupCounts1306(a)| <= |a|
  ensures forall v :: v in GroupCounts1306(a) ==> 0 <= v <= |a|
  decreases |a|
{
  if |a| > 0 {
    var r := RemoveAll1306(a[1..], a[0]);
    GCtsFacts1306(r);
    CountLe1306(a, a[0]);
  }
}

ghost function GC1306(a: seq<int>): nat
  decreases |a|
{
  if |a| == 0 then 1 else 10 * |a| + 10 + GC1306(RemoveAll1306(a[1..], a[0]))
}

lemma GCBound1306(a: seq<int>)
  ensures GC1306(a) <= 10 * (|a| * |a|) + 10 * |a| + 1
  decreases |a|
{
  if |a| > 0 {
    var r := RemoveAll1306(a[1..], a[0]);
    var m := |a| - 1;
    GCBound1306(r);
    CostMulMonoLeft(|r|, m, |r|);
    CostMulMono(m, |r|, m);
    assert |a| * |a| == m * m + 2 * m + 1 by { CostMulDistrib(m, 1, |a|, |a|); CostMulDistrib(m, 1, |a|, m); }
  }
}

ghost function SD1306(c: seq<int>): nat
  decreases |c|
{
  if |c| == 0 then 1 else 6 + SD1306(c[1..])
}

lemma SDBound1306(c: seq<int>)
  ensures SD1306(c) == 6 * |c| + 1
  decreases |c|
{
  if |c| > 0 { SDBound1306(c[1..]); }
}

lemma MaxLe1306(s: seq<int>, i: nat, best: int, N: int)
  requires i <= |s| && best <= N
  requires forall v :: v in s ==> v <= N
  ensures MaxSeqFrom(s, i, best) <= N
  decreases |s| - i
{
  if i < |s| {
    assert s[i] in s;
    MaxLe1306(s, i + 1, if s[i] > best then s[i] else best, N);
  }
}

lemma Sq1306(N: nat, K: nat)
  requires K == 6 * N + 12
  ensures (N + 1) * K == 6 * (N * N) + 18 * N + 12
{
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 17 * (|a_list| * |a_list|) + 60 * |a_list| + 60 + |output|
{
  steps := 1;
  ghost var N := |a_list|;
  var counts := GroupCounts1306(a_list);
  GCtsFacts1306(a_list);
  GCBound1306(a_list);
  steps := steps + GC1306(a_list);
  var maxC := if |counts| > 0 then MaxSeq(counts) else 0;
  if |counts| > 0 {
    MaxLe1306(counts, 1, counts[0], N);
    assert counts[0] in counts;
  }
  steps := steps + 6 * |counts| + 4;
  var day := 1;
  ghost var K: nat := 6 * N + 12;
  ghost var B := steps;
  while day <= maxC + 1 && SumDiv1306(counts, day) >= n
    invariant 1 <= day <= maxC + 2
    invariant maxC <= N
    invariant |counts| <= N
    invariant steps <= B + (day - 1) * K
    decreases maxC + 2 - day
  {
    SDBound1306(counts);
    CostMulDistrib(day - 1, 1, day, K);
    day := day + 1;
    steps := steps + 6 * |counts| + 8;
  }
  CostMulMonoLeft(day - 1, N + 1, K);
  Sq1306(N, K);
  IntToStringDigits(day - 1);
  output := IntToString(day - 1);
  steps := steps + Digits(day - 1);
}
