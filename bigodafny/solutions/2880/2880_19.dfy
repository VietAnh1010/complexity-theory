// 774_C. Maximum Number  (problem 2880, solution 2880_19)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a=int(input())
// sstring=[]
// if a%2:
//    sstring.append('7')
// else:
//    a=a
// if a%2:
//    a=a-3
// else:
//    a=a
// for i in range (a // 2):
//    sstring.append('1')
// print(''.join(sstring))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var a := n;
  var parts: seq<string> := [];
  if a % 2 == 1 {
    parts := parts + ["7"];
  }
  if a % 2 == 1 {
    a := a - 3;
  }
  var raw := a / 2;
  var cnt := if raw < 0 then 0 else raw;
  var i := 0;
  while i < cnt
    invariant 0 <= i <= cnt
    decreases cnt - i
  {
    parts := parts + ["1"];
    i := i + 1;
  }
  output := Join(parts, "");
}
