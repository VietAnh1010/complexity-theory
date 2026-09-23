// 454_B. Little Pony and Sort by Shift  (problem 71, solution 71_217)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// #for x in range(len(a)):
// #    a[x]=int(a[x])
// # print(x)
// ans=0
// d=0
// for x in range(1,n):
//     if(a[x-1]>a[x]):
//         d=1
//         if(sorted(a)==a[x:]+a[:x]):
//             ans=n-x
//         else:
//             ans=-1
//         break
// if(d==0):
//     print(0)
// else:
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// SortInts's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k
// recurrence, bounded O(k log k) -- precedent solutions-proved/1871/1871_156.dfy.
// The loop is linear; at most one iteration does the rotation check, whose
// two slices, concatenation and sequence equality are each O(n), charged
// as such since seq `==` isn't in the fixed-cost table rows.

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 8 * n + |output| + 10
{
  steps := 1;
  var sortedA := SortInts(a_list);
  SortCostTreeBound(|a_list|);
  steps := steps + SortCost(|a_list|);
  var ans := 0;
  var d := 0;
  var x := 1;
  var doneFlag := false;
  ghost var base1 := steps;
  while x < n && !doneFlag
    invariant 1 <= x <= n
    invariant steps <= base1 + 4 * (x - 1) + (if doneFlag then 4 * n else 0)
    decreases n - x
  {
    if a_list[x - 1] > a_list[x] {
      d := 1;
      if sortedA == a_list[x..] + a_list[..x] {
        ans := n - x;
      } else {
        ans := -1;
      }
      doneFlag := true;
      steps := steps + 4 * n;
    }
    x := x + 1;
    steps := steps + 4;
  }
  assert steps <= base1 + 4 * (n - 1) + 4 * n;
  if d == 0 {
    output := IntToString(0);
  } else {
    output := IntToString(ans);
  }
  steps := steps + |output| + 2;
}
