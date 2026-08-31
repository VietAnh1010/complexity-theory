// 624_B. Making a String  (problem 209, solution 209_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(sorted(map(int, input().split()), reverse=True))
// for i in range(n - 1):
//     a[i + 1] = max(0, min(a[i] - 1, a[i + 1]))
// print(sum(a))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string)
{
  var a := Sort(numbers, (x, y) => x > y);
  var i := 0;
  while i < N - 1
    decreases N - 1 - i
  {
    var cand := a[i] - 1;
    if a[i + 1] < cand { cand := a[i + 1]; }
    if cand < 0 { cand := 0; }
    a := a[i + 1 := cand];
    i := i + 1;
  }
  var total := 0;
  var j := 0;
  while j < |a|
    decreases |a| - j
  {
    total := total + a[j];
    j := j + 1;
  }
  output := IntToString(total);
}
