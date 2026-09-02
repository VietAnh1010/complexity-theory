// 952_C. Ravioli Sort  (problem 1765, solution 1765_73)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # ===================================
// # (c) MidAndFeed aka ASilentVoice
// # ===================================
// # import math 
// # import collections
// # ===================================
// n = int(input())
// q = [int(x) for x in input().split()]
// for i in range(n-1):
// 	if abs(q[i]-q[i+1]) > 1:
// 		print("NO")
// 		break
// else:
// 	print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var ok := true;
  var i := 0;
  while i < n - 1 && ok
    decreases if ok then n - 1 - i else 0
  {
    if AbsInt(a_list[i] - a_list[i + 1]) > 1 {
      ok := false;
    }
    i := i + 1;
  }
  output := if ok then "YES" else "NO";
}
