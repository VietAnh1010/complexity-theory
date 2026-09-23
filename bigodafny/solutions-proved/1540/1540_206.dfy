// 873_A. Chores  (problem 1540, solution 1540_206)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k,x=map(int,input().split())
// a=list(map(int,input().split()))
// a.sort(reverse=True)
// for i in range(0,k):
//     a[i]=x
// print(sum(a))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  requires 0 <= a <= n
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 3 * n + 6
{
  SortCostTreeBound(n);
  steps := 1 + SortCost(n);
  ghost var s0 := steps;
  var sortedA := SortInts(numbers);
  var keep := n - a;
  var total := 0;
  var i := 0;
  while i < keep
    invariant 0 <= i <= keep
    invariant steps == s0 + 3 * i
    decreases keep - i
  {
    total := total + sortedA[i];
    i := i + 1;
    steps := steps + 3;
  }
  total := total + a * b;
  output := IntToString(total);
  steps := steps + 4;
}
