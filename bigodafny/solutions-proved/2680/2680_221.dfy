// 546_C. Soldier and Cards  (problem 2680, solution 2680_221)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// NOTE ON THE BOUND: the loop is capped by the literal k<=1000 in the source,
// so under the stipulated charge table (s[a..b] costs 1, s+t costs |t|, both
// flat regardless of the slice's real length) every iteration costs a fixed
// small constant and the whole loop is O(1). CPython's a[1:] is really
// O(len(a)); that real per-iteration cost, not this proof's, is where the
// label's O(n+m) comes from. relation: tighter-costmodel.

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, list1: seq<int>, list2: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 20000
{
  steps := 1;
  var a := list1;
  var b := list2;
  var k := 0;
  while |a| > 0 && |b| > 0 && k <= 1000
    invariant 0 <= k <= 1001
    invariant steps <= 1 + 15 * k
    decreases 1001 - k
  {
    var a0 := a[0];
    var b0 := b[0];
    if a0 > b0 && !(a0 == 0 && b0 == 9) && !(a0 == 9 && b0 == 0) {
      a := a[1..] + [b0, a0];
      b := b[1..];
    } else {
      b := b[1..] + [a0, b0];
      a := a[1..];
    }
    k := k + 1;
    steps := steps + 15;
  }
  if |a| != 0 && |b| != 0 {
    output := "-1";
  } else if |a| > 0 {
    output := JoinInts([k, 1], " ");
  } else {
    output := JoinInts([k, 2], " ");
  }
  steps := steps + 4;
}
