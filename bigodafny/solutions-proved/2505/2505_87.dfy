// 886_C. Petya and Catacombs  (problem 2505, solution 2505_87)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = list(map(int, input().split()))
// arr.sort()
// cnt_total = 0
// cnt_tmp = 0
// for i in range(1,n):
//     if arr[i] == arr[i-1]:
//         cnt_total +=1
// print(cnt_total+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires |coordinates| >= 1
  requires n <= |coordinates[0]|
  requires n >= 0
  ensures steps <= 2 * |coordinates[0]| * (CeilLog2(|coordinates[0]|) + 1) + 3 * n + 4
{
  var arr := SortInts(coordinates[0]);
  SortCostTreeBound(|coordinates[0]|);
  var cnt := 0;
  var i := 1;
  steps := 1 + SortCost(|coordinates[0]|);
  ghost var base1 := steps;
  while i < n
    invariant 1 <= i <= n + 1
    invariant |arr| == |coordinates[0]|
    invariant steps <= base1 + 3 * (i - 1)
    decreases n - i
  {
    if arr[i] == arr[i - 1] {
      cnt := cnt + 1;
    }
    i := i + 1;
    steps := steps + 3;
  }
  output := IntToString(cnt + 1);
  steps := steps + 1;
}
