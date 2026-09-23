// 440_A. Forgotten Episode  (problem 2742, solution 2742_0)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input=sys.stdin.buffer.readline
//
// n=int(input())
// arr=list(map(int,input().split()))
// arr.sort()
// z=0
// for i in range(0,n-1):
// 	if arr[i]==i+1:
// 		continue
// 	else:
// 		print(i+1)
// 		z=1
// 		break
// if z==0:
// 	print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(nlogn), confirmed. The sort is charged SortCost and bounded by the
// prelude's SortCostNLogN, the tight recursion-tree argument. The loop itself
// runs at most N-1 iterations, exiting early via z.
method Solve(N: int, values: seq<int>) returns (output: string, ghost steps: nat)
  requires N == |values|
  ensures steps <= 2 * NLogN(|values|) + 5 * |values| + 5
{
  SortCostNLogN(|values|);
  steps := 1 + SortCost(|values|);
  var arr := SortInts(values);
  assert |arr| == |values|;
  var z := 0;
  var i := 0;
  output := "";
  while i < N - 1 && z == 0
    invariant 0 <= i <= N
    invariant steps <= 1 + SortCost(|values|) + 2 * i + 2
    decreases (if N - 1 - i > 0 then N - 1 - i else 0)
  {
    if i < |arr| && arr[i] == i + 1 {
      // continue
    } else {
      output := IntToString(i + 1) + "\n";
      z := 1;
    }
    i := i + 1;
    steps := steps + 2;
  }
  if z == 0 {
    output := IntToString(N) + "\n";
  }
  steps := steps + 1;
}
