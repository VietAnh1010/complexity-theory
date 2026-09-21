// p03523 CODE FESTIVAL 2017 Final - AKIBA  (problem 831, solution 831_74)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import re
//
// S = input()
// print('YES' if re.match(r'^A?KIHA?BA?RA?$', S) else 'NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// All four loop bounds are the literal 2, independent of |word|: 16 fixed
// candidate strings are built and compared regardless of input. O(1).
method Solve(word: string) returns (output: string, ghost steps: nat)
  ensures steps <= 400
{
  steps := 1;
  var matched := false;
  var i1 := 0;
  ghost var base1 := steps;
  while i1 <= 1 && !matched
    invariant 0 <= i1 <= 2
    invariant steps <= base1 + 190 * i1
    decreases 2 - i1
  {
    var i2 := 0;
    ghost var base2 := steps;
    while i2 <= 1 && !matched
      invariant 0 <= i2 <= 2
      invariant steps <= base2 + 45 * i2
      decreases 2 - i2
    {
      var i3 := 0;
      ghost var base3 := steps;
      while i3 <= 1 && !matched
        invariant 0 <= i3 <= 2
        invariant steps <= base3 + 10 * i3
        decreases 2 - i3
      {
        var i4 := 0;
        ghost var base4 := steps;
        while i4 <= 1 && !matched
          invariant 0 <= i4 <= 2
          invariant steps <= base4 + 2 * i4
          decreases 2 - i4
        {
          var cand := (if i1 == 1 then "A" else "") + "KIH" + (if i2 == 1 then "A" else "") + "B" + (if i3 == 1 then "A" else "") + "R" + (if i4 == 1 then "A" else "");
          if cand == word {
            matched := true;
          }
          i4 := i4 + 1;
          steps := steps + 2;
        }
        i3 := i3 + 1;
        steps := steps + 6;
      }
      i2 := i2 + 1;
      steps := steps + 25;
    }
    i1 := i1 + 1;
    steps := steps + 100;
  }
  if matched {
    output := "YES\n";
  } else {
    output := "NO\n";
  }
  steps := steps + 1;
}
