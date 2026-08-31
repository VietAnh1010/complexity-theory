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

method Solve(word: string) returns (output: string)
{
  var matched := false;
  var i1 := 0;
  while i1 <= 1 && !matched
    decreases 2 - i1
  {
    var i2 := 0;
    while i2 <= 1 && !matched
      decreases 2 - i2
    {
      var i3 := 0;
      while i3 <= 1 && !matched
        decreases 2 - i3
      {
        var i4 := 0;
        while i4 <= 1 && !matched
          decreases 2 - i4
        {
          var cand := (if i1 == 1 then "A" else "") + "KIH" + (if i2 == 1 then "A" else "") + "B" + (if i3 == 1 then "A" else "") + "R" + (if i4 == 1 then "A" else "");
          if cand == word {
            matched := true;
          }
          i4 := i4 + 1;
        }
        i3 := i3 + 1;
      }
      i2 := i2 + 1;
    }
    i1 := i1 + 1;
  }
  if matched {
    output := "YES\n";
  } else {
    output := "NO\n";
  }
}
