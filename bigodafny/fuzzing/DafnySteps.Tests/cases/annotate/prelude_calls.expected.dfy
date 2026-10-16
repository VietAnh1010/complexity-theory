include "../../../../prelude.dfy"

method Solve(a: seq<int>, words: seq<string>)
    returns (output: string, ghost steps: nat)
{
  steps := 0;
  steps := steps + SortCost(|a|);
  var sorted := SortInts(a);
  steps := steps + |sorted|;
  var m := MaxSeq(sorted);
  steps := steps + (SumLen(words) + |words|);
  var line := Join(words, " ");
  steps := steps + (Digits(m) + |IntToString(m)| + |"-"| * 3 + |Repeat("-", 3)|);
  output := line + IntToString(m) + Repeat("-", 3);
}

import opened Prelude
