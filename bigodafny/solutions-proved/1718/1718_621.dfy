// 489_B. BerSU Ball  (problem 1718, solution 1718_621)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// m = int(input())
// b = [int(x) for x in input().split()]
//
// a = sorted(a)
// b = sorted(b)
//
// idx_a = 0
// idx_b = 0
// cnt = 0
// while(idx_a < n and idx_b < m):
//
// 	if( abs(a[idx_a]-b[idx_b]) <= 1):
// 		idx_a+=1
// 		idx_b+=1
// 		cnt+=1
//
// 	elif(a[idx_a]>b[idx_b]):
// 		idx_b+=1
// 	else:
// 		idx_a+=1
//
// print(cnt)
// #FernandezFernandez2019
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N1: int, list1: seq<int>, N2: int, list2: seq<int>) returns (output: string, ghost steps: nat)
  requires N1 <= |list1|
  requires N2 <= |list2|
  ensures steps <= 2 * NLogN(|list1|) + 2 * NLogN(|list2|)
                 + 6 * (if N1 > 0 then N1 else 0) + 6 * (if N2 > 0 then N2 else 0) + 10
{
  steps := 1;
  var a := SortInts(list1);
  steps := steps + SortCost(|list1|);
  SortCostWithin(|list1|, |list1|);
  var b := SortInts(list2);
  steps := steps + SortCost(|list2|);
  SortCostWithin(|list2|, |list2|);
  var ia := 0;
  var ib := 0;
  var cnt := 0;
  while ia < N1 && ib < N2
    invariant 0 <= ia <= (if N1 > 0 then N1 else 0)
    invariant 0 <= ib <= (if N2 > 0 then N2 else 0)
    invariant |a| == |list1| && |b| == |list2|
    invariant steps <= 2 * NLogN(|list1|) + 2 * NLogN(|list2|) + 6 * (ia + ib) + 5
    decreases N1 - ia + N2 - ib
  {
    if AbsInt(a[ia] - b[ib]) <= 1 {
      ia := ia + 1;
      ib := ib + 1;
      cnt := cnt + 1;
    } else if a[ia] > b[ib] {
      ib := ib + 1;
    } else {
      ia := ia + 1;
    }
    steps := steps + 6;
  }
  output := IntToString(cnt);
  steps := steps + 4;
}
