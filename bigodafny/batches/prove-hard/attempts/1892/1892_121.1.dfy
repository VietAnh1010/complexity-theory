// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// flag1=0
// flag2=0
// for i in range(n):
// 	if l[i]==2:
// 		flag1=1
// 		break
// for i in range(n):
// 	if l[i]==1:
// 		flag2=1
// 		break
// if flag1==0 or flag2==0:
// 	print(*l)
// else:
// 	print(2,1,end=' ')
// 	l.remove(2)
// 	l.remove(1)
// 	l.sort(reverse=True)
// 	print(*l)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

function RemoveFirst(l: seq<int>, x: int): seq<int>
  decreases |l|
{
  if |l| == 0 then
    []
  else if l[0] == x then
    l[1..]
  else
    [l[0]] + RemoveFirst(l[1..], x)
}

ghost function RemoveFirst_steps(l: seq<int>, x: int): nat
  decreases |l|
{
  3 + if |l| == 0 then 0 else 3 + if l[0] == x then 1 else 3 + RemoveFirst_steps(l[1..], x) + |RemoveFirst(l[1..], x)|
}

lemma RFLen(l: seq<int>, x: int)
  ensures |RemoveFirst(l, x)| <= |l|
  decreases |l|
{
  if |l| > 0 && l[0] != x { RFLen(l[1..], x); }
}

lemma RFSteps(l: seq<int>, x: int)
  ensures RemoveFirst_steps(l, x) <= |l| * |l| + 10 * |l| + 3
  decreases |l|
{
  if |l| > 0 && l[0] != x {
    RFSteps(l[1..], x);
    RFLen(l[1..], x);
    var k := |l|;
    assert (k - 1) * (k - 1) == k * k - 2 * k + 1;
  }
}

ghost function Q(n: nat): nat { n * n + 10 * n + 3 }

lemma RFStepsWithin(l: seq<int>, x: int, N: nat)
  requires |l| <= N
  ensures RemoveFirst_steps(l, x) <= Q(N)
{
  RFSteps(l, x);
  CostMulMonoLeft(|l|, N, |l|);
  CostMulMono(N, |l|, N);
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n <= |a_list|
  ensures steps <= 2 * NLogN(|a_list|) + 2 * Q(|a_list|) + 14 * |a_list| + 20 + 2 * |output|
{
  ghost var N := |a_list|;
  steps := 0;
  var l := a_list;
  var flag1 := false;
  var flag2 := false;
  var i := 0;
  while i < n && !flag1
    invariant 0 <= i <= N
    invariant steps <= 7 * i
    decreases !flag1, n - i
  {
    steps := steps + (3 + if i < n then 1 else 0);
    steps := steps + 2;
    if l[i] == 2 {
      flag1 := true;
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + (2 + if i < n then 1 else 0);
  i := 0;
  while i < n && !flag2
    invariant 0 <= i <= N
    invariant steps <= 7 * N + 3 + 7 * i
    decreases !flag2, n - i
  {
    steps := steps + (3 + if i < n then 1 else 0);
    steps := steps + 2;
    if l[i] == 1 {
      flag2 := true;
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + (2 + if i < n then 1 else 0);
  steps := steps + (2 + if !flag1 then 0 else 1);
  if !flag1 || !flag2 {
    if |l| >= 1 { JoinIntsLen(l, " "); }
    steps := steps + (SumDigits(l) + |l|);
    output := JoinInts(l, " ");
  } else {
    RFStepsWithin(l, 2, N);
    RFLen(l, 2);
    steps := steps + RemoveFirst_steps(l, 2);
    var rest := RemoveFirst(l, 2);
    RFStepsWithin(rest, 1, N);
    RFLen(rest, 1);
    steps := steps + RemoveFirst_steps(rest, 1);
    rest := RemoveFirst(rest, 1);
    SortCostWithin(|rest|, N);
    steps := steps + SortCost(|rest|);
    var descending := Sort(rest, (x: int, y: int) => x > y);
    if |descending| >= 1 { JoinIntsLen(descending, " "); }
    steps := steps + (SumDigits(descending) + |descending| + |JoinInts(descending, " ")|);
    output := "2 1 " + JoinInts(descending, " ");
  }
}

import opened Prelude
