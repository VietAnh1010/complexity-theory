// 750_A. New Year and Hurry  (problem 704, solution 704_351)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n, k = map(int, input().split())
// 
// timeToSolve = 240 - k
// problems = math.floor(timeToSolve / 5)
// problems = math.floor((math.sqrt(1 + 8*problems) - 1) / 2)
// 
// print(n if problems > n else problems)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
