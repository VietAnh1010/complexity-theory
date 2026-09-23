// 432_A. Choosing Teams  (problem 2166, solution 2166_288)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int,input().split())
// y = map(int,input().split())
// z = sorted(y)
// k = 5-k
// if(k<0):
// 	print("0")
// else:
// 	count = 0
// 	for i in z:
// 		if(i<=k):
// 			count = count+1
// print(int(count/3))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |numbers| * (CeilLog2(|numbers|) + 1) + 4 * |numbers| + 7
{
  SortCostTreeBound(|numbers|);
  steps := 1 + SortCost(|numbers|);
  ghost var s0 := steps;
  var z := SortInts(numbers);
  var k2 := 5 - k;
  steps := steps + 2;
  if k2 < 0 {
    output := "0";
    steps := steps + 1;
  } else {
    var count := 0;
    var i := 0;
    while i < |z|
      invariant 0 <= i <= |z|
      invariant steps == s0 + 2 + 4 * i
      decreases |z| - i
    {
      if z[i] <= k2 { count := count + 1; }
      i := i + 1;
      steps := steps + 4;
    }
    output := IntToString(FloorDiv(count, 3));
    steps := steps + 3;
  }
}
