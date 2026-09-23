// p02994 AtCoder Beginner Contest 131 - Bite Eating  (problem 2313, solution 2313_104)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, l = map(int, input().split())
// s = [0] * n
// for i in range(n):
//     s[i] = i + l
// s.sort(key=abs)
// print(sum(s[1:]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound (see
// solutions-proved/nlogn/603/603_284.dfy for the same argument) ----------

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  requires a >= 1
  ensures steps <= 2 * a * (CeilLog2(a) + 1) + 2 * a + 5
{
  var n := a;
  var l := b;
  steps := 1;
  var s: seq<int> := seq(n, i requires 0 <= i < n => i + l);
  steps := steps + n;
  SortCostTreeBound(n);
  steps := steps + SortCost(n);
  var sorted := Sort(s, (x: int, y: int) => AbsInt(x) < AbsInt(y));
  assert |sorted| == n;
  var total := SumSeq(sorted[1..]);
  steps := steps + n;
  output := IntToString(total);
  steps := steps + 1;
}
