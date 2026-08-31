// 471_A. MUH and Sticks  (problem 2036, solution 2036_120)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// sticksL = input().split()
// for i in sticksL:
//     lNum = sticksL.count(i)
//     if (lNum > 3):
//         break
// sticksL = set(sticksL)
// if(lNum > 3 and (len(sticksL) == 3 or (len(sticksL) == 2 and lNum > 4))):
//     print("Bear")
// elif(lNum > 3):
//     print("Elephant")
// else:
//     print("Alien")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
