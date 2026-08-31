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
  var num := n;
  var m := 1 + 8 * num;
  // find largest k >= 0 with (2k+1)^2 <= m  (== floor((sqrt(m)-1)/2))
  var lo := 0;
  var hi := num + 2;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if (2 * mid + 1) * (2 * mid + 1) <= m {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  var k := lo - 1;
  var summa := k * (k + 1) / 2;
  if num == summa {
    k := k - 1;
    summa := k * (k + 1) / 2;
  }
  var result := num - summa;
  output := IntToString(result);
}
