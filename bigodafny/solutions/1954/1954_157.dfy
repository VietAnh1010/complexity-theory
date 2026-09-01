// p02927 Japanese Student Championship 2019 Qualification - Takahashi Calendar  (problem 1954, solution 1954_157)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// mm, dd = map(int, input().split())
// 
// count = 0
// for d in range(1, dd + 1):
//     d1 = d % 10
//     d10 = d // 10
//     m = d1 * d10
//     if d1 >1 and d10 > 1 and m <= mm:
//         count += 1
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var count := 0;
  var d := 1;
  while d <= b
    decreases b - d + 1
  {
    var d1 := d % 10;
    var d10 := d / 10;
    var m := d1 * d10;
    if d1 > 1 && d10 > 1 && m <= a {
      count := count + 1;
    }
    d := d + 1;
  }
  output := IntToString(count);
}
