// 1102_C. Doors Breaking and Repairing  (problem 2982, solution 2982_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,y=input().split()
// n=int(n)
// x=int(x)
// y=int(y)
//
// l=[int(x) for x in input().split()]
//
// l.sort()
//
// count_a=0
//
//
// for i in range(n):
// 	if(l[i]<=x):
// 		count_a+=1
//
// if(x>y):
// 	print(n)
//
// else:
// 	print((count_a%2)+(count_a//2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound (see
// solutions-proved/nlogn/603/603_284.dfy for the same argument) ----------

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires a >= 0
  ensures steps <= 2 * |d_list| * (CeilLog2(|d_list|) + 1) + 3 * a + 10
{
  steps := 1;
  var n := a;
  var x := b;
  var y := c;
  SortCostTreeBound(|d_list|);
  steps := steps + SortCost(|d_list|);
  var l := SortInts(d_list);
  assert |l| == |d_list|;
  var countA := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + SortCost(|d_list|) + 3 * i
    decreases n - i
  {
    if i < |l| && l[i] <= x { countA := countA + 1; }
    i := i + 1;
    steps := steps + 3;
  }
  if x > y {
    output := IntToString(n);
  } else {
    output := IntToString((countA % 2) + (countA / 2));
  }
  steps := steps + 3;
}
