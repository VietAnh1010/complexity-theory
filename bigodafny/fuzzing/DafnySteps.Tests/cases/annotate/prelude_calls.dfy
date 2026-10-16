// Prelude functions are charged per COMPLEXITY.md. The include stays an include.
include "../../../../prelude.dfy"
import opened Prelude

method Solve(a: seq<int>, words: seq<string>) returns (output: string)
{
  var sorted := SortInts(a);
  var m := MaxSeq(sorted);
  var line := Join(words, " ");
  output := line + IntToString(m) + Repeat("-", 3);
}
