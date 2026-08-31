// 651_B. Beautiful Paintings  (problem 1054, solution 1054_212)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// from collections import Counter
// input = sys.stdin.readline
// 
// n = int(input())
// a = dict(Counter(sorted(input().split())))
// 
// ans = 0
// f = 0
// for val in a:
//     ans += min(f, a[val])
//     f += max(a[val] - f, 0)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
