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

method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  ensures steps <= 800   // O(1): the loop bound 100 is a literal in the source
{
  var li: seq<int> := [];
  var i := 0;
  var p := 1;
  steps := 2;
  while i < 100
    invariant 0 <= i <= 100
    invariant |li| <= i
    invariant steps <= 6 * i + 2
    decreases 100 - i
  {
    if p >= a && p <= b {
      li := li + [p];
      steps := steps + 1;
    }
    steps := steps + 2;
    p := p * c;
    i := i + 1;
    steps := steps + 2;
  }
  if |li| == 0 {
    output := "-1\n";
    steps := steps + 1;
  } else {
    output := JoinInts(li, " ") + "\n";
    steps := steps + |li| + 1;   // Join over |li| IntToString'd parts, exception applies
  }
}
