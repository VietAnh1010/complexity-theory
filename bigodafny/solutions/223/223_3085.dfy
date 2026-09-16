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

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var s := SortInts(a_list);
  var i := 0;
  var j := |s| - 1;
  var res := 0;
  while i < j
    invariant 0 <= i
    invariant j < |s|
    invariant i <= j + 1
    decreases j - i
  {
    if s[i] + s[j] <= 4 {
      s := s[j := s[j] + s[i]];
      i := i + 1;
    } else {
      j := j - 1;
      res := res + 1;
    }
  }
  output := IntToString(res + 1);
}
