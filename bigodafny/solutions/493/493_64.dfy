// p03957 CODE FESTIVAL 2016 qual C - CF  (problem 493, solution 493_64)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// if 'C' in s and 'F' in s and s.index('C') < s.rindex('F'):
//     print('Yes')
// else:
//     print('No')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  var hasC := false;
  var hasF := false;
  var firstC := 0;
  var lastF := 0;
  var i := 0;
  while i < |string_|
    decreases |string_| - i
  {
    if string_[i] == 'C' && !hasC {
      hasC := true;
      firstC := i;
    }
    if string_[i] == 'F' {
      hasF := true;
      lastF := i;
    }
    i := i + 1;
  }
  if hasC && hasF && firstC < lastF {
    output := "Yes\n";
  } else {
    output := "No\n";
  }
}
