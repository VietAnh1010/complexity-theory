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

ghost function Sq1306(x: nat): nat { x * x }
ghost function Cube1306(x: nat): nat { x * x * x }

lemma CubeMono1306(x: nat, y: nat)
  requires x <= y
  ensures Cube1306(x) <= Cube1306(y)
{
  CostMulMonoLeft(x, y, x);
  CostMulMono(y, x, y);
  CostMulMonoLeft(x * x, y * y, x);
  CostMulMono(y * y, x, y);
}

lemma CountFacts1306(a: seq<int>, v: int)
  ensures CountOccur1306_steps(a, v) == 8 * |a| + 3
  ensures 0 <= CountOccur1306(a, v) <= |a|
  decreases |a|
{
  if |a| > 0 { CountFacts1306(a[1..], v); }
}

lemma RemoveSteps1306(a: seq<int>, v: int)
  ensures RemoveAll1306_steps(a, v) <= Sq1306(|a|) + 9 * |a| + 3
  decreases |a|
{
  if |a| > 0 {
    RemoveSteps1306(a[1..], v);
    var n := |a|;
    assert Sq1306(n - 1) == Sq1306(n) - 2 * n + 1 by {
      assert (n - 1) * (n - 1) == n * n - 2 * n + 1;
    }
    assert |RemoveAll1306(a[1..], v)| <= n - 1;
  }
}

lemma GroupFacts1306(a: seq<int>)
  ensures |GroupCounts1306(a)| <= |a|
  ensures forall x :: x in GroupCounts1306(a) ==> x <= |a|
  ensures GroupCounts1306_steps(a) <= 8 * Cube1306(|a| + 1)
  decreases |a|
{
  if |a| > 0 {
    var rem := RemoveAll1306(a[1..], a[0]);
    var n := |a|;
    GroupFacts1306(rem);
    CountFacts1306(a, a[0]);
    RemoveSteps1306(a[1..], a[0]);
    assert |rem| <= n - 1;
    GroupArith1306(n, |rem|, CountOccur1306_steps(a, a[0]), RemoveAll1306_steps(a[1..], a[0]),
                   GroupCounts1306_steps(rem), |GroupCounts1306(rem)|);
    assert GroupCounts1306(a) == [CountOccur1306(a, a[0])] + GroupCounts1306(rem);
  }
}

lemma GroupArith1306(n: nat, m: nat, c: nat, r: nat, g: nat, gl: nat)
  requires n >= 1 && m + 1 <= n
  requires c == 8 * n + 3
  requires r <= Sq1306(n - 1) + 9 * (n - 1) + 3
  requires g <= 8 * Cube1306(m + 1)
  requires gl <= m
  ensures 3 + (4 + c + r + g + gl) <= 8 * Cube1306(n + 1)
{
  CubeMono1306(m + 1, n);
  assert Sq1306(n - 1) == Sq1306(n) - 2 * n + 1 by {
    assert (n - 1) * (n - 1) == n * n - 2 * n + 1;
  }
  assert Cube1306(n + 1) == Cube1306(n) + 3 * Sq1306(n) + 3 * n + 1 by {
    assert (n + 1) * (n + 1) * (n + 1) == n * n * n + 3 * (n * n) + 3 * n + 1;
  }
  CostMulMono(n, 0, n);
  assert Sq1306(n) >= 0;
}

lemma MaxFromLe1306(s: seq<int>, i: nat, best: int, bd: int)
  requires i <= |s|
  requires best <= bd
  requires forall k :: i <= k < |s| ==> s[k] <= bd
  ensures MaxSeqFrom(s, i, best) <= bd
  decreases |s| - i
{
  if i < |s| { MaxFromLe1306(s, i + 1, if s[i] > best then s[i] else best, bd); }
}

lemma SumDivSteps1306(counts: seq<int>, day: int)
  requires day > 0
  ensures SumDiv1306_steps(counts, day) <= 3 + 7 * |counts|
  decreases |counts|
{
  if |counts| > 0 { SumDivSteps1306(counts[1..], day); }
}

lemma LinBound1306(n: nat)
  ensures (n + 1) * (10 + 7 * n) <= 7 * Sq1306(n + 1) + 3 * (n + 1)
{
  assert (n + 1) * (10 + 7 * n) == 7 * (n * n) + 17 * n + 10;
  assert Sq1306(n + 1) == n * n + 2 * n + 1;
}

method Solve(n: int, k: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 8 * Cube1306(|a_list| + 1) + 7 * Sq1306(|a_list| + 1) + 11 * |a_list| + 20 + |output|
{
  steps := 0;
  steps := steps + GroupCounts1306_steps(a_list);
  var counts := GroupCounts1306(a_list);
  steps := steps + (3 + if |counts| > 0 then |counts| else 0);
  var maxC := if |counts| > 0 then MaxSeq(counts) else 0;
  ghost var S0 := steps;
  ghost var K := 10 + 7 * |a_list|;
  GroupFacts1306(a_list);
  assert forall j :: 0 <= j < |counts| ==> counts[j] <= |a_list| by {
    forall j | 0 <= j < |counts| ensures counts[j] <= |a_list| { assert counts[j] in counts; }
  }
  if |counts| > 0 { MaxFromLe1306(counts, 1, counts[0], |a_list|); }
  assert maxC <= |a_list|;
  var day := 1;
  while day <= maxC + 1 && SumDiv1306(counts, day) >= n
    invariant 1 <= day <= |a_list| + 2
    invariant steps <= S0 + (day - 1) * K
    decreases maxC + 2 - day
  {
    SumDivSteps1306(counts, day);
    steps := steps + (4 + if day <= maxC + 1 then 1 + SumDiv1306_steps(counts, day) else 0);
    steps := steps + 1;
    day := day + 1;
    CostMulDistrib(day - 2, 1, day - 1, K);
  }
  SumDivSteps1306(counts, day);
  CostMulMonoLeft(day - 1, |a_list| + 1, K);
  LinBound1306(|a_list|);
  steps := steps + (3 + if day <= maxC + 1 then 1 + SumDiv1306_steps(counts, day) else 0);
  steps := steps + (1 + Digits(day - 1));
  output := IntToString(day - 1);
  IntToStringDigits(day - 1);
}

import opened Prelude
