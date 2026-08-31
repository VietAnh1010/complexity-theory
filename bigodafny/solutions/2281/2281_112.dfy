// 349_A. Cinema Line  (problem 2281, solution 2281_112)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x= int(input())
// total1 = 0
// total2=0
// C = "YES"
// f = [int(i) for i in input().split()]
// for z in f:
//    if z == 25:
//       total1 += 1
//    elif z==50:
//       if total1 >=1:
//             total1 -= 1
//             total2 +=1
//       else:
//             C = "NO"
//             break
//    else:
//       if total1 >=1 and total2>=1:
//             total1 -=1
//             total2 -=1
//       elif total1 >=3:
//             total1 -=3
//       else:
//             C = "NO"
//             break
// print(C)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
