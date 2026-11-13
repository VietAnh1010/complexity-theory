// 137_B. Permutation  (problem 1413, solution 1413_104)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// ns = [int(x) for x in input().split()]
// ok = [False]*n
// for ni in ns:
//     ni-=1
//     if ni<n:
//         ok[ni]=True
// print(sum([1 for isOK in ok if not isOK]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires forall k :: 0 <= k < |values| ==> values[k] >= 1
  ensures steps <= 9 * |values| + 7 * n + |output| + 5
{
  steps := 1;
  var ok := seq(n, i => false);
  steps := steps + n;
  var idx := 0;
  while idx < |values|
    invariant |ok| == n
    invariant 0 <= idx <= |values|
    invariant steps == 9 * idx + n + 1
    decreases |values| - idx
  {
    var ni := values[idx] - 1;
    if ni < n {
      var realIdx := if ni >= 0 then ni else ni + n;
      ok := ok[realIdx := true];
    }
    idx := idx + 1;
    steps := steps + 9;
  }
  var cnt := 0;
  var j := 0;
  ghost var s0 := steps;
  while j < n
    invariant 0 <= j && |ok| == n
    invariant j <= n
    invariant steps == s0 + 6 * j
    decreases n - j
  {
    if !ok[j] { cnt := cnt + 1; }
    j := j + 1;
    steps := steps + 6;
  }
  output := IntToString(cnt);
  IntToStringDigits(cnt);
  steps := steps + Digits(cnt);
}
