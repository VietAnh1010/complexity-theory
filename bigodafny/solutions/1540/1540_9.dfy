// 873_A. Chores  (problem 1540, solution 1540_9)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #873A
// 
// given = input().split(" ")
// tasks = input().split(" ")
// 
// nominal = 0
// for i in range(len(tasks) - int(given[1])):
//     nominal += int(tasks[i])
// 
// total = nominal + int(given[1])*int(given[2])
// 
// print(total)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
