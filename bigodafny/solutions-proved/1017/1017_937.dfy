// 1331_D. Again?  (problem 1017, solution 1017_937)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input()
// num=int(n[6])-48
// if num%2==0:
//   print(0)
// else:
//   print(1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  requires |s| == 7
  ensures steps <= 10
{
  steps := 0;
  var d := s[6] as int - '0' as int;
  steps := steps + 4;
  if d % 2 == 0 {
    output := "0";
    steps := steps + 2;
  } else {
    output := "1";
    steps := steps + 2;
  }
}
