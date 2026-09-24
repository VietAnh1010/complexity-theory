// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1616)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int,input().split()))
// count = 0
//
// for i in range(1,len(a)):
// 	if a[i] in a[:i]:
// 		count += 1
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt1434a(xs: seq<int>, v: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == v then true
  else ContainsInt1434a(xs[1..], v)
}

method Solve(values: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 + (|values| + 1) * (|values| + 3)
{
  steps := 1;
  ghost var ibase := steps;
  ghost var K := |values| + 3;
  var count := 0;
  var i := 1;
  while i < |values|
    invariant 1 <= i <= |values| + 1
    invariant steps <= ibase + i * K
    decreases |values| - i
  {
    ghost var i_old := i;
    // ContainsInt1434a scans values[..i]: charge its length, plus 1 for the slice.
    var contained := ContainsInt1434a(values[..i], values[i]);
    steps := steps + 1 + i;
    if contained {
      count := count + 1;
      steps := steps + 1;
    }
    i := i + 1;
    steps := steps + 1;
    assert steps <= ibase + i_old * K + K;
    CostMulDistrib(i_old, 1, i_old + 1, K);
    assert i_old * K + K == (i_old + 1) * K;
  }
  CostMulMonoLeft(i, |values| + 1, K);
  output := IntToString(count);
  steps := steps + 1;
}
