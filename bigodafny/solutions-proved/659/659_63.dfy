// 127_B. Canvas Frames  (problem 659, solution 659_63)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// a.sort()
// b,t,c=[],1,0
// for i in range(n):
//     if i==n-1 or a[i]!=a[i+1]:
//         c+=t//4
//         if t%4>=2:b.append(t%2)
//         t=1
//     else:t+=1
// print(len(b)//2+c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound (see
// solutions-proved/nlogn/603/603_284.dfy for the same argument) ----------

method Solve(n: int, ratings: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |ratings| * (CeilLog2(|ratings|) + 1) + 5 * |ratings| + 5
{
  steps := 1;
  SortCostTreeBound(|ratings|);
  steps := steps + SortCost(|ratings|);
  var a := SortInts(ratings);
  assert |a| == |ratings|;
  var bLen := 0;
  var t := 1;
  var c := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant steps <= 1 + SortCost(|ratings|) + 4 * i
    decreases |a| - i
  {
    if i == |a| - 1 || a[i] != a[i+1] {
      c := c + t / 4;
      if t % 4 >= 2 { bLen := bLen + 1; }
      t := 1;
    } else {
      t := t + 1;
    }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(bLen / 2 + c);
  steps := steps + 1;
}
