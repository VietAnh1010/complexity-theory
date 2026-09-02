// 650_A. Watchmen  (problem 1853, solution 1853_66)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// n = int(input())
// a, b = [], []
// for i in range(n):
//     ai, bi = [int(x) for x in input().split()]
//     a.append(ai)
//     b.append(bi)
// sum = 0
// for k, v in dict(Counter(a)).items():
//     if v > 1:
//        sum += v*(v-1)//2
// for k, v in dict(Counter(b)).items():
//     if v > 1:
//        sum += v*(v-1)//2
// r = [(x, y) for x, y in zip(a, b)]
// for k, v in dict(Counter(r)).items():
//     if v > 1:
//        sum -= v*(v-1)//2
// print(sum)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<(int, int)>) returns (output: string)
{
  var total := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    var j := i + 1;
    while j < n
      decreases n - j
    {
      if coordinates[i].0 == coordinates[j].0 || coordinates[i].1 == coordinates[j].1 {
        total := total + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  output := IntToString(total);
}
