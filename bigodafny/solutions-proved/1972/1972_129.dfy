// 614_A. Link/Cut Tree  (problem 1972, solution 1972_129)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l,r,k = map(int,input().split())
// li = [k**i for i in range(100) if k**i >= l and k**i <= r]
// if len(li) == 0:
//     print(-1)
// else:
//     print(' '.join([str(s) for s in li]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Instrumented copy: the loop trip count is the literal 100 in the source,
// not a function of a or b or c -- a fixed constant, so O(1). |li| <= 100 too,
// so the final Join is bounded by a constant regardless of a, b, c.
method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  ensures steps <= 700
{
  steps := 1;
  var li: seq<int> := [];
  var i := 0;
  var p := 1;
  while i < 100
    invariant 0 <= i <= 100
    invariant |li| <= i
    invariant steps <= 1 + 4 * i
  {
    if p >= a && p <= b {
      li := li + [p];
      steps := steps + 1;
    }
    steps := steps + 1;
    p := p * c;
    i := i + 1;
    steps := steps + 2;
  }
  if |li| == 0 {
    output := "-1\n";
    steps := steps + 1;
  } else {
    output := JoinInts(li, " ") + "\n";
    steps := steps + (2 * |li| + 1) + 1;   // JoinInts: |li| IntToString calls (1 each) + Join cost |li|-ish + final concat
  }
}
