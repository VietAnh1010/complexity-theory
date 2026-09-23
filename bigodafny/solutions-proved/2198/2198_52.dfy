// 788_A. Functions again  (problem 2198, solution 2198_52)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
//
// b = []
// for i in range(n - 1):
//     b.append(abs(a[i] - a[i + 1]))
//
// c = []
// s = 1
// summ = 0
// for i in range(n - 1):
//     summ += s * b[i]
//     s = -s
//     c.append(summ)
//
// c.sort()
//
// if c[0] < 0:
//     print(c[n - 2] - c[0])
// else:
//     print(c[n - 2])
// --------------------------------------------------------------------
//
// PROOF NOTE (relation: confirms). SortInts(c) costs SortCost(n-1), bounded
// by the prelude's SortCostNLogN, the tight recursion-tree argument, so the
// proved bound is O(n log n).

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 2
  requires n <= |a_list|
  ensures steps <= 2 * NLogN(n - 1) + 1 + 8 * n + 10
{
  var b: seq<int> := [];
  var i := 0;
  steps := 3;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |b| == i
    invariant steps <= 4 * i + 3
    decreases n - 1 - i
  {
    b := b + [AbsInt(a_list[i] - a_list[i+1])];
    i := i + 1;
    steps := steps + 4;
  }
  var c: seq<int> := [];
  var s := 1;
  var summ := 0;
  i := 0;
  steps := steps + 3;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |b| == n - 1
    invariant |c| == i
    invariant steps <= 4 * n + 4 * i + 6
    decreases n - 1 - i
  {
    summ := summ + s * b[i];
    s := -s;
    c := c + [summ];
    i := i + 1;
    steps := steps + 4;
  }
  assert steps <= 8 * n + 2;
  SortCostNLogN(n - 1);
  var sortedC := SortInts(c);
  steps := steps + SortCost(n - 1);
  assert steps <= SortCost(n - 1) + 8 * n + 2;
  var result := if sortedC[0] < 0 then sortedC[n-2] - sortedC[0] else sortedC[n-2];
  output := IntToString(result);
  steps := steps + 4;
  assert steps <= SortCost(n - 1) + 8 * n + 6;
}
