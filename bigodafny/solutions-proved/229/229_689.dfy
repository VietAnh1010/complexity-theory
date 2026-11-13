// 677_A. Vanya and Fence  (problem 229, solution 229_689)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// c=map(int,input().split())
// d=0
// for i in c:
//     if i>b:
//         d+=2
//     else:
//         d+=1
// print(d)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 5 * |a_list| + |output| + 3
{
  steps := 1;
  var d := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps == 1 + 5 * i
    decreases |a_list| - i
  {
    if a_list[i] > k {
      d := d + 2;
    } else {
      d := d + 1;
    }
    i := i + 1;
    steps := steps + 5;
  }
  output := IntToString(d);
  IntToStringDigits(d);
  steps := steps + 1 + |output|;
}
