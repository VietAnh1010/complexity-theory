// 296_A. Yaroslav and Permutations  (problem 2266, solution 2266_298)
// time complexity: O(n)
// python exact-diff baseline: exact

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 5 * |a_list| + 3
{
  steps := 1;
  var freq: map<string, int> := map[];
  var maximum := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= 5 * i + 1
    decreases |a_list| - i
  {
    var v := a_list[i];
    var c := if v in freq then freq[v] + 1 else 1;
    freq := freq[v := c];
    if c > maximum { maximum := c; }
    i := i + 1;
    steps := steps + 5;
  }
  if maximum <= (n + 1) / 2 {
    output := "YES";
  } else {
    output := "NO";
  }
  steps := steps + 1;
}
