// 471_A. MUH and Sticks  (problem 2036, solution 2036_19)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// ls = [0] * 9
// for i in input().split():
//     ls[int(i) - 1] += 1
// x = [i for i in ls if i > 0]
// if x == [6] or x == [2, 4] or x == [4, 2]:
//     print("Elephant")
// elif x == [1,1,4] or x == [1,4,1] or x == [4,1,1] or x == [1,5] or x == [5,1]:
//     print("Bear")
// else:
//     print("Alien")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
