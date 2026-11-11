// --- Python ---------------------------------------------------------
// n = int(input())
// boys = list(map(int, input().split()))
// m = int(input())
// girls = list(map(int, input().split()))
// boys.sort()
// girls.sort()
// mark = [0]*m
// for i in range(n):
//     for j in range(m):
//         #print("{} {}".format(i, j))
//         if mark[j] == 0 and abs(boys[i] - girls[j]) <= 1:
//             #print("{} {}".format(i, j))
//             mark[j] = 1
//             break
// print(mark.count(1))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(N1: int, list1: seq<int>, N2: int, list2: seq<int>)
    returns (output: string, ghost steps: nat)
  requires 0 <= N1 <= |list1|
  requires 0 <= N2 <= |list2|
  ensures steps <= 2 * NLogN(|list1|) + 2 * NLogN(|list2|) + 15 * (N1 * N2) + 6 * N1 + N2 + 3 + |output|
{
  steps := 0;
  steps := steps + SortCost(|list1|);
  var boys := SortInts(list1);
  steps := steps + SortCost(|list2|);
  var girls := SortInts(list2);
  steps := steps + N2;
  var mark := seq(N2, (idx: int) => 0);
  var cnt := 0;
  var bi := 0;
  ghost var base := steps;
  ghost var K := 15 * N2 + 6;
  while bi < N1
    invariant 0 <= bi <= N1
    invariant steps <= base + bi * K
    invariant |mark| == N2
    invariant |boys| == |list1| && |girls| == |list2|
    decreases N1 - bi
  {
    ghost var sOut := steps;
    steps := steps + 2;
    var gj := 0;
    var matched := false;
    while gj < N2 && !matched
      invariant 0 <= gj <= N2
      invariant steps <= sOut + 2 + 15 * gj
      invariant |mark| == N2
      decreases N2 - gj
    {
      steps := steps + (3 + if gj < N2 then 1 else 0);
      steps := steps + (3 + if mark[gj] == 0 then 4 + 1 else 0);
      if mark[gj] == 0 && AbsInt(boys[bi] - girls[gj]) <= 1 {
        steps := steps + 1;
        mark := mark[gj := 1];
        matched := true;
        steps := steps + 1;
        cnt := cnt + 1;
      }
      steps := steps + 1;
      gj := gj + 1;
    }
    steps := steps + (2 + if gj < N2 then 1 else 0);
    steps := steps + 1;
    CostMulDistrib(bi, 1, bi + 1, K);
    bi := bi + 1;
  }
  steps := steps + 1;
  steps := steps + Digits(cnt);
  SortCostWithin(|list1|, |list1|);
  SortCostWithin(|list2|, |list2|);
  ProdLemma(N1, N2);
  IntToStringDigits(cnt);
  output := IntToString(cnt);
}

import opened Prelude

lemma ProdLemma(a: nat, b: nat)
  ensures a * (15 * b + 6) == 15 * (a * b) + 6 * a
{
}
