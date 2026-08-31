// 1201_B. Zero Array  (problem 2010, solution 2010_401)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// inp = input()
// a=[int(ele) for ele in inp.split()]
// a.sort()
// count=0
// for ele in a:
//     if ele%2!=0:
//         count += 1
// if sum(a[:n-1]) < a[-1]:
//     print('NO')
// elif count%2==0:
//     print('YES')
// else:
//     print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
