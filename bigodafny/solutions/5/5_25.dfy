// 622_A. Infinite Sequence  (problem 5, solution 5_25)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// number = input()
// current = 0
// num = int(number)
// D = math.sqrt(1 + 8*num)
// n = ( D - 1 )/2
// n = int(n)
// summa = n*(n+1)/2
// if num == summa:
// 	n-=1
// 	summa = n*(n+1)/2
// if num>summa:
// 	num -= summa
// num = int (num)
// print (num)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
