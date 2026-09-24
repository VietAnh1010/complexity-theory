// 158_B. Taxi  (problem 223, solution 223_3085)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = list(map(int, input().split()))
//
// s.sort()
//
// i, j = 0, len(s)-1
// res = 0
//
// while i<j:
//     if s[i]+s[j]<=4:
//         s[j] += s[i]
//         i += 1
//     else:
//         j -= 1
//         res += 1
//
// print(res+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|a_list|) + 3 * |a_list| + 4
{
  steps := 1;
  var s := SortInts(a_list);
  assert |s| == |a_list|;
  steps := steps + SortCost(|a_list|);
  var i := 0;
  var j := |s| - 1;
  var res := 0;
  while i < j
    invariant |s| == |a_list|
    invariant 0 <= i
    invariant j < |s|
    invariant i <= j + 1
    invariant steps <= 1 + SortCost(|a_list|) + 3 * (i + (|a_list| - 1 - j))
    decreases j - i
  {
    if s[i] + s[j] <= 4 {
      s := s[j := s[j] + s[i]];
      i := i + 1;
    } else {
      j := j - 1;
      res := res + 1;
    }
    steps := steps + 3;
  }
  assert i + (|a_list| - 1 - j) <= |a_list|;
  assert steps <= 1 + SortCost(|a_list|) + 3 * |a_list|;
  SortCostNLogN(|a_list|);
  assert steps <= 2 * NLogN(|a_list|) + 3 * |a_list| + 2;
  output := IntToString(res + 1);
  steps := steps + 2;
}
