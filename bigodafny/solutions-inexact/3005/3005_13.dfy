// p02417 Counting Characters  (problem 3005, solution 3005_13)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// s=sys.stdin.read().lower()
// a=[print(i,':',s.count(i)) for i in map(chr,range(97,123))]
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string) returns (output: string)
{
  var lines: seq<string> := [];
  var letter := 0;
  while letter < 26
    invariant 0 <= letter <= 26
    decreases 26 - letter
  {
    var c: char := (97 + letter) as char;
    var count := 0;
    var i := 0;
    while i < |text|
      invariant 0 <= i <= |text|
      decreases |text| - i
    {
      var ch := text[i];
      var lc: char := if ch >= 'A' && ch <= 'Z' then ((ch as int) + 32) as char else ch;
      if lc == c {
        count := count + 1;
      }
      i := i + 1;
    }
    lines := lines + [[c] + " : " + IntToString(count)];
    letter := letter + 1;
  }
  output := Join(lines, "\n");
}
