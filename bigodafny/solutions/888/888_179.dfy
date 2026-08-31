// 1358_D. The Best Vacation  (problem 888, solution 888_179)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sumprog(a, b):
//     return (a + b) * (b - a + 1) // 2
//  
//  
// n, x = map(int, input().split())
// d = list(map(int, input().split())) * 2
// max_hugs = 0
// i = 0
// j = 0
// days = 0
// hugs = 0
// while i < n:
//     if days + d[j] <= x:
//         days += d[j]
//         hugs += sumprog(1, d[j])
//         j += 1
//     else:
//         max_hugs = max(max_hugs, hugs + sumprog(d[j] - (x - days) + 1, d[j]))
//         hugs -= sumprog(1, d[i])
//         days -= d[i]
//         i += 1
// print(max_hugs)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string)
{
  var d := a_list + a_list;
  var max_hugs := 0;
  var i := 0;
  var j := 0;
  var days := 0;
  var hugs := 0;
  while i < n
    decreases n - i
  {
    if days + d[j] <= m {
      days := days + d[j];
      hugs := hugs + SumProg(1, d[j]);
      j := j + 1;
    } else {
      var cand := hugs + SumProg(d[j] - (m - days) + 1, d[j]);
      if cand > max_hugs { max_hugs := cand; }
      hugs := hugs - SumProg(1, d[i]);
      days := days - d[i];
      i := i + 1;
    }
  }
  output := IntToString(max_hugs) + "\n";
}

function SumProg(a: int, b: int): int
{
  (a + b) * (b - a + 1) / 2
}
