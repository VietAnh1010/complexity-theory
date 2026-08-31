// 1032_A. Kitchen Utensils  (problem 138, solution 138_449)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// n, m = [int(s) for s in input().split()]
// a = [int(s) for s in input().split()]
// # c, d = np.unique(a), np.unique(a, return_counts=True)[1]
// c = []
// cnt = 0
// for o in a:
//     if o not in c:
//         c.append(o)
// d = []
// for i in c:
// 	d.append(a.count(i))
// dishes, set = ceil(max(d) / m), len(c) #���������� ����, ������� � ����� ����
// eta = dishes * set * m
// print(eta - n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
{
  var sorted := SortInts(numbers);
  var m := |sorted|;
  var maxCount := 0;
  var distinct := 0;
  var i := 0;
  while i < m
    decreases m - i
  {
    var j := i;
    while j < m && sorted[j] == sorted[i]
      decreases m - j
    {
      j := j + 1;
    }
    var cnt := j - i;
    if cnt > maxCount {
      maxCount := cnt;
    }
    distinct := distinct + 1;
    i := j;
  }
  var dishes := if maxCount % k == 0 then maxCount / k else maxCount / k + 1;
  var eta := dishes * distinct * k;
  output := IntToString(eta - n);
}
