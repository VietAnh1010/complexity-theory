// 489_B. BerSU Ball  (problem 1718, solution 1718_1166)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

// PROOF NOTE (relation: looser-structural).
// Both input lists are sorted in full, then each of the first N1 boys scans at
// most N2 girls. The proved bound is O(N1*N2 + n log n + m log m) with
// n = |list1|, m = |list2|. The label O(n*m) omits the two sorts, which are
// real in the Python too (both lists are sorted before matching) and dominate
// when one side is small: at m = 1 the sort of the other side is n log n
// against a label of n. The sorts are bounded by the prelude's SortCostNLogN.

include "../../prelude.dfy"
import opened Prelude

lemma ProdSplit1718(a: nat, b: nat)
  ensures a * (4 * b + 3) == 4 * a * b + 3 * a
{
}

method Solve(N1: int, list1: seq<int>, N2: int, list2: seq<int>) returns (output: string, ghost steps: nat)
  requires 0 <= N1 <= |list1|
  requires 0 <= N2 <= |list2|
  ensures steps <= 2 * NLogN(|list1|) + 2 * NLogN(|list2|) + 4 * N1 * N2 + 3 * N1 + N2 + 6
{
  var boys := SortInts(list1);
  var girls := SortInts(list2);
  steps := 1 + SortCost(|list1|) + SortCost(|list2|);
  SortCostNLogN(|list1|);
  SortCostNLogN(|list2|);
  var mark := seq(N2, (idx: int) => 0);
  steps := steps + N2;
  ghost var base := steps;
  ghost var K: nat := 4 * N2 + 3;
  var cnt := 0;
  var bi := 0;
  while bi < N1
    invariant 0 <= bi <= N1
    invariant |mark| == N2
    invariant |boys| == |list1| && |girls| == |list2|
    invariant steps <= base + bi * K
    decreases N1 - bi
  {
    ghost var s0 := steps;
    var gj := 0;
    var matched := false;
    while gj < N2 && !matched
      invariant 0 <= gj <= N2
      invariant |mark| == N2
      invariant steps == s0 + 4 * gj
      decreases N2 - gj
    {
      if mark[gj] == 0 && AbsInt(boys[bi] - girls[gj]) <= 1 {
        mark := mark[gj := 1];
        matched := true;
        cnt := cnt + 1;
      }
      gj := gj + 1;
      steps := steps + 4;
    }
    bi := bi + 1;
    steps := steps + 3;
    CostMulDistrib(bi - 1, 1, bi, K);
  }
  ProdSplit1718(N1, N2);
  output := IntToString(cnt);
  steps := steps + 2;
}
