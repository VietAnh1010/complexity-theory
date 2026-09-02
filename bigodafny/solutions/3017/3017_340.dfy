// 202_A. LLPS  (problem 3017, solution 3017_340)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// k=0
// t=0
// for i in range(len(s)):
//     if ord(s[i])>k:
//         k=ord(s[i])
//         t=s[i]
// print(str(t)*s.count(chr(k)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  var k := 0;
  var t: char := ' ';
  var i := 0;
  while i < |string_|
    invariant 0 <= i <= |string_|
    decreases |string_| - i
  {
    var code := string_[i] as int;
    if code > k {
      k := code;
      t := string_[i];
    }
    i := i + 1;
  }
  var count: nat := 0;
  i := 0;
  while i < |string_|
    invariant 0 <= i <= |string_|
    decreases |string_| - i
  {
    if (string_[i] as int) == k {
      count := count + 1;
    }
    i := i + 1;
  }
  output := Repeat([t], count);
}
