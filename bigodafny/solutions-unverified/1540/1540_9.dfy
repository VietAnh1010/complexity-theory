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
  var keep := |numbers| - a;
  var nominal := 0;
  var i := 0;
  while i < keep
    decreases keep - i
  {
    nominal := nominal + numbers[i];
    i := i + 1;
  }
  var total := nominal + a * b;
  output := IntToString(total);
}
