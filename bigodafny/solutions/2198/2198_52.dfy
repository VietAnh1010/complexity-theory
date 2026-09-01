// 788_A. Functions again  (problem 2198, solution 2198_52)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// 
// b = []
// for i in range(n - 1):
//     b.append(abs(a[i] - a[i + 1]))
// 
// c = []
// s = 1
// summ = 0
// for i in range(n - 1):
//     summ += s * b[i]
//     s = -s
//     c.append(summ)
// 
// c.sort()
// 
// if c[0] < 0:
//     print(c[n - 2] - c[0])
// else:
//     print(c[n - 2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var b: seq<int> := [];
  var i := 0;
  while i < n - 1
    decreases n - 1 - i
  {
    b := b + [AbsInt(a_list[i] - a_list[i+1])];
    i := i + 1;
  }
  var c: seq<int> := [];
  var s := 1;
  var summ := 0;
  i := 0;
  while i < n - 1
    decreases n - 1 - i
  {
    summ := summ + s * b[i];
    s := -s;
    c := c + [summ];
    i := i + 1;
  }
  var sortedC := SortInts(c);
  var result := if sortedC[0] < 0 then sortedC[n-2] - sortedC[0] else sortedC[n-2];
  output := IntToString(result);
}
