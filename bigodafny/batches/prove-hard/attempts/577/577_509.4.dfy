// --- Python ---------------------------------------------------------
// check=[2]
// i=0
// while check[-1]<=10**9:
//     check.append(check[-1]+3*i+5)
//     i+=1
// from bisect import bisect_right
// def dfs(x):
//     if x<2:
//         return 0
//     return dfs(x-check[bisect_right(check,x)-1])+1
// for _ in range(int(input())):
//     n=int(input())
//     print(dfs(n))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, numbers_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires forall t :: 0 <= t < |numbers_list| ==> numbers_list[t] >= 0
  ensures steps <= 2800000007 + 10 * |numbers_list| + 1400000020 * PrefixSum(numbers_list, |numbers_list|) + 2 * |output|
{
  steps := 0;
  steps := steps + 1;
  var check := [2];
  var i := 0;
  while check[|check| - 1] <= 1000000000
    invariant |check| >= 1
    invariant check[0] == 2
    invariant forall t :: 0 <= t < |check| ==> check[t] >= 2
    invariant i == |check| - 1
    invariant check[|check| - 1] >= 5 * i + 2
    invariant i <= 200000000
    invariant steps <= 1 + 14 * i
    decreases 200000000 - i
  {
    steps := steps + 5;
    steps := steps + (7 + |[check[|check| - 1] + 3 * i + 5]|);
    check := check + [check[|check| - 1] + 3 * i + 5];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 4;
  var results: seq<string> := [];
  var k := 0;
  while k < |numbers_list|
    invariant 0 <= k <= |numbers_list|
    invariant |results| == k
    invariant steps <= 2800000005 + 9 * k + 1400000020 * PrefixSum(numbers_list, k) + SumLen(results)
    decreases |numbers_list| - k
  {
    DfsBound(check, numbers_list[k]);
    IntToStringDigits(Dfs(check, numbers_list[k]));
    SumLenSnoc(results, IntToString(Dfs(check, numbers_list[k])));
    assert PrefixSum(numbers_list, k + 1) == PrefixSum(numbers_list, k) + numbers_list[k];
    steps := steps + 3;
    steps := steps + (2 + Dfs_steps(check, numbers_list[k]) + Digits(Dfs(check, numbers_list[k])) + |[IntToString(Dfs(check, numbers_list[k]))]|);
    results := results + [IntToString(Dfs(check, numbers_list[k]))];
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 2;
  steps := steps + (SumLen(results) + |results|);
  output := Join(results, "\n");
  if |results| >= 1 { JoinLen(results, "\n"); }
}

function FindIdxFrom(check: seq<int>, x: int, i: int, best: int): int
  requires 0 <= i <= |check|
  requires 0 <= best < |check|
  requires check[best] <= x
  ensures 0 <= FindIdxFrom(check, x, i, best) < |check|
  ensures check[FindIdxFrom(check, x, i, best)] <= x
  decreases |check| - i
{
  if i >= |check| then
    best
  else if check[i] <= x then
    FindIdxFrom(check, x, i + 1, i)
  else
    FindIdxFrom(check, x, i + 1, best)
}

ghost function FindIdxFrom_steps(check: seq<int>, x: int, i: int, best: int): nat
  requires 0 <= i <= |check|
  requires 0 <= best < |check|
  requires check[best] <= x
  decreases |check| - i
{
  3 + if i >= |check| then 0 else 3 + if check[i] <= x then 1 + FindIdxFrom_steps(check, x, i + 1, i) else 1 + FindIdxFrom_steps(check, x, i + 1, best)
}

function Dfs(check: seq<int>, x: int): int
  requires |check| > 0
  requires check[0] == 2
  requires forall t :: 0 <= t < |check| ==> check[t] >= 2
  requires x >= 0
  decreases x
{
  if x < 2 then
    0
  else
    1 + Dfs(check, x - check[FindIdxFrom(check, x, 0, 0)])
}

ghost function Dfs_steps(check: seq<int>, x: int): nat
  requires |check| > 0
  requires check[0] == 2
  requires forall t :: 0 <= t < |check| ==> check[t] >= 2
  requires x >= 0
  decreases x
{
  2 + if x < 2 then 0 else 3 + FindIdxFrom_steps(check, x, 0, 0) + Dfs_steps(check, x - check[FindIdxFrom(check, x, 0, 0)])
}

lemma FisBound(check: seq<int>, x: int, i: int, best: int)
  requires 0 <= i <= |check|
  requires 0 <= best < |check|
  requires check[best] <= x
  ensures FindIdxFrom_steps(check, x, i, best) <= 3 + 7 * (|check| - i)
  decreases |check| - i
{
  if i < |check| {
    if check[i] <= x { FisBound(check, x, i + 1, i); } else { FisBound(check, x, i + 1, best); }
  }
}

lemma DfsBound(check: seq<int>, x: int)
  requires |check| > 0
  requires check[0] == 2
  requires forall t :: 0 <= t < |check| ==> check[t] >= 2
  requires x >= 0
  requires |check| <= 200000002
  ensures Dfs_steps(check, x) <= 2 + 1400000020 * x
  decreases x
{
  if x >= 2 {
    FisBound(check, x, 0, 0);
    DfsBound(check, x - check[FindIdxFrom(check, x, 0, 0)]);
  }
}

import opened Prelude
