// p03346 AtCoder Grand Contest 024 - Backfront  (problem 785, solution 785_12)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// P = list(int(input()) for _ in range(n))
// tmp = [0]*(n+1)
// for p in P:
//     tmp[p] = tmp[p-1] + 1
// print(n-max(tmp))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var tmp := new int[n+1];
  var i := 0;
  while i < |numbers|
    decreases |numbers| - i
  {
    var p := numbers[i];
    if 0 < p <= n {
      tmp[p] := tmp[p-1] + 1;
    }
    i := i + 1;
  }
  var mx := tmp[0];
  i := 1;
  while i <= n
    decreases n - i
  {
    if tmp[i] > mx { mx := tmp[i]; }
    i := i + 1;
  }
  output := IntToString(n - mx);
}
