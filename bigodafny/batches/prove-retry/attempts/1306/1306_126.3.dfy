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

include "../../../../prelude.dfy"

function CountOccur1306(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then
    0
  else
    (if a[0] == v then 1 else 0) + CountOccur1306(a[1..], v)
}

ghost function CountOccur1306_steps(a: seq<int>, v: int): nat
  decreases |a|
{
  3 + if |a| == 0 then 0 else 5 + CountOccur1306_steps(a[1..], v)
}

function RemoveAll1306(a: seq<int>, v: int): seq<int>
  ensures |RemoveAll1306(a, v)| <= |a|
  decreases |a|
{
  if |a| == 0 then
    []
  else if a[0] == v then
    RemoveAll1306(a[1..], v)
  else
    [a[0]] + RemoveAll1306(a[1..], v)
}

ghost function RemoveAll1306_steps(a: seq<int>, v: int): nat
  decreases |a|
{
  3 + if |a| == 0 then 0 else 3 + if a[0] == v then 1 + RemoveAll1306_steps(a[1..], v) else 3 + RemoveAll1306_steps(a[1..], v) + |RemoveAll1306(a[1..], v)|
}

function GroupCounts1306(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then
    []
  else
    [CountOccur1306(a, a[0])] + GroupCounts1306(RemoveAll1306(a[1..], a[0]))
}

ghost function GroupCounts1306_steps(a: seq<int>): nat
  decreases |a|
{
  3 + if |a| == 0 then 0 else 4 + CountOccur1306_steps(a, a[0]) + RemoveAll1306_steps(a[1..], a[0]) + GroupCounts1306_steps(RemoveAll1306(a[1..], a[0])) + |GroupCounts1306(RemoveAll1306(a[1..], a[0]))|
}

function SumDiv1306(counts: seq<int>, day: int): int
  requires day > 0
  decreases |counts|
{
  if |counts| == 0 then
    0
  else
    counts[0] / day + SumDiv1306(counts[1..], day)
}

ghost function SumDiv1306_steps(counts: seq<int>, day: int): nat
  requires day > 0
  decreases |counts|
{
  3 + if |counts| == 0 then 0 else 4 + SumDiv1306_steps(counts[1..], day)
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

lemma CountStepsBound1306(a: seq<int>, v: int)
  ensures CountOccur1306_steps(a, v) == 8 * |a| + 3
  decreases |a|
{
  if |a| > 0 { CountStepsBound1306(a[1..], v); }
}

opaque ghost function RemoveCap1306(n: nat): nat
{
  n * n + 9 * n + 3
}

opaque ghost function GroupCap1306(n: nat): nat
{
  n * (n * n + 18 * n + 21) + 3
}

lemma RemoveArith1306(N: nat)
  requires N >= 1
  ensures RemoveCap1306(N - 1) + N + 8 <= RemoveCap1306(N)
{
  reveal RemoveCap1306();
  var m := N - 1;
  assert N * N == m * m + 2 * m + 1 by { CostMulDistrib(m, 1, N, N); CostMulDistrib(m, 1, N, m); }
}

lemma RemoveStepsBound1306(a: seq<int>, v: int)
  ensures RemoveAll1306_steps(a, v) <= RemoveCap1306(|a|)
  decreases |a|
{
  if |a| == 0 {
    reveal RemoveCap1306();
  } else {
    RemoveStepsBound1306(a[1..], v);
    RemoveArith1306(|a|);
  }
}

lemma GroupArith1306(N: nat, R: nat)
  requires N >= 1 && R <= N - 1
  ensures RemoveCap1306(N - 1) + 8 * N + R + 10 + GroupCap1306(R) <= GroupCap1306(N)
{
  reveal RemoveCap1306();
  reveal GroupCap1306();
  var m := N - 1;
  var q := N * N + 18 * N + 21;
  var qr := R * R + 18 * R + 21;
  assert N * N == m * m + 2 * m + 1 by { CostMulDistrib(m, 1, N, N); CostMulDistrib(m, 1, N, m); }
  CostMulMonoLeft(R, N, R);
  CostMulMono(N, R, N);
  CostMulMono(R, qr, q);
  CostMulMonoLeft(R, m, q);
  CostMulDistrib(m, 1, N, q);
}

lemma GroupStepsBound1306(a: seq<int>)
  ensures GroupCounts1306_steps(a) <= GroupCap1306(|a|)
  decreases |a|
{
  if |a| == 0 {
    reveal GroupCap1306();
  } else {
    var r := RemoveAll1306(a[1..], a[0]);
    GroupStepsBound1306(r);
    GCtsFacts1306(r);
    CountStepsBound1306(a, a[0]);
    RemoveStepsBound1306(a[1..], a[0]);
    GroupArith1306(|a|, |r|);
  }
}

lemma GroupCapValue1306(n: nat)
  ensures GroupCap1306(n) == n * (n * n + 18 * n + 21) + 3
{
  reveal GroupCap1306();
}

lemma SumDivSteps1306(c: seq<int>, day: int)
  requires day > 0
  ensures SumDiv1306_steps(c, day) == 7 * |c| + 3
  decreases |c|
{
  if |c| > 0 { SumDivSteps1306(c[1..], day); }
}

lemma LoopTotal1306(N: nat, K: nat)
  requires K == 7 * N + 9
  ensures (N + 1) * K == 7 * (N * N) + 16 * N + 9
{
}

method Solve(n: int, k: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= |a_list| * (|a_list| * |a_list| + 18 * |a_list| + 21) + 7 * (|a_list| * |a_list|) + 24 * |a_list| + 23 + |output|
{
  steps := 0;
  ghost var N := |a_list|;
  steps := steps + GroupCounts1306_steps(a_list);
  GroupStepsBound1306(a_list);
  GroupCapValue1306(N);
  var counts := GroupCounts1306(a_list);
  GCtsFacts1306(a_list);
  steps := steps + (3 + if |counts| > 0 then |counts| else 0);
  var maxC := if |counts| > 0 then MaxSeq(counts) else 0;
  if |counts| > 0 {
    assert counts[0] in counts;
    MaxLe1306(counts, 1, counts[0], N);
    MaxSeqBound(counts);
  }
  var day := 1;
  ghost var K: nat := 7 * N + 9;
  ghost var B := steps;
  while day <= maxC + 1 && SumDiv1306(counts, day) >= n
    invariant 1 <= day <= maxC + 2
    invariant maxC <= N
    invariant |counts| <= N
    invariant steps <= B + (day - 1) * K
    decreases maxC + 2 - day
  {
    SumDivSteps1306(counts, day);
    steps := steps + (4 + if day <= maxC + 1 then 1 + SumDiv1306_steps(counts, day) else 0);
    steps := steps + 1;
    CostMulDistrib(day - 1, 1, day, K);
    day := day + 1;
  }
  SumDivSteps1306(counts, day);
  steps := steps + (3 + if day <= maxC + 1 then 1 + SumDiv1306_steps(counts, day) else 0);
  CostMulMonoLeft(day - 1, N + 1, K);
  LoopTotal1306(N, K);
  IntToStringDigits(day - 1);
  steps := steps + (1 + Digits(day - 1));
  output := IntToString(day - 1);
}

import opened Prelude
