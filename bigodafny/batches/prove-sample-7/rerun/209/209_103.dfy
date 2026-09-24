// 624_B. Making a String  (problem 209, solution 209_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(sorted(map(int, input().split()), reverse=True))
// for i in range(n - 1):
//     a[i + 1] = max(0, min(a[i] - 1, a[i + 1]))
// print(sum(a))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires N == |numbers|
  ensures steps <= 2 * NLogN(N) + 4 * N + 5
{
  steps := 1;
  var a := Sort(numbers, (x, y) => x > y);
  assert |a| == N;
  steps := steps + SortCost(N);
  var i := 0;
  while i < N - 1
    invariant 0 <= i <= N
    invariant |a| == N
    invariant steps <= 1 + SortCost(N) + 2 * i
    decreases N - 1 - i
  {
    var cand := a[i] - 1;
    if a[i + 1] < cand { cand := a[i + 1]; }
    if cand < 0 { cand := 0; }
    a := a[i + 1 := cand];
    i := i + 1;
    steps := steps + 2;
  }
  assert steps <= 1 + SortCost(N) + 2 * N;
  var total := 0;
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant steps <= 1 + SortCost(N) + 2 * N + 2 * j
    decreases |a| - j
  {
    total := total + a[j];
    j := j + 1;
    steps := steps + 2;
  }
  assert steps <= 1 + SortCost(N) + 4 * N;
  SortCostNLogN(N);
  assert steps <= 2 * NLogN(N) + 4 * N + 2;
  output := IntToString(total);
  steps := steps + 3;
}
