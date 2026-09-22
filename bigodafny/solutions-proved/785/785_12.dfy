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

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 10 * |numbers| + 10 * n + 10
{
  steps := 1;
  var tmp := seq(n+1, _ => 0);
  var i := 0;
  ghost var b1 := steps;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |tmp| == n + 1
    invariant steps <= b1 + 6 * i
    decreases |numbers| - i
  {
    var p := numbers[i];
    if 0 < p <= n {
      tmp := tmp[p := tmp[p-1] + 1];
    }
    i := i + 1;
    steps := steps + 6;
  }
  var mx := tmp[0];
  i := 1;
  ghost var b2 := steps;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |tmp| == n + 1
    invariant steps <= b2 + 4 * (i - 1)
    decreases n - i
  {
    if tmp[i] > mx { mx := tmp[i]; }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(n - mx);
  steps := steps + 2;
}
