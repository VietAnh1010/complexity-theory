// 350_A. TL  (problem 305, solution 305_76)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// a = list(map(int, input().split()))
// b = list(map(int, input().split()))
// a.sort()
// b.sort()
// am = a[0]
// bm = min(b)
// i = b[0] - 1
// while i >= 2*am and a[-1] <= i and i > 0:
//     i -= 1
// i+=1
// if i == 0 or not(i >= 2*am and a[-1] <= i and i > 0) or bm <= i:
//     print(-1)
// else:
//     print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
