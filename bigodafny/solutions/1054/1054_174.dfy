// 651_B. Beautiful Paintings  (problem 1054, solution 1054_174)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = list(map(int, input().split()))
// d = {}
// for i in l:
//     if i not in d:
//         d[i] = 1
//     else:
//         d[i] += 1
// 
// m = max(d.values())
// print(n - m)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var counts: map<int, int> := map[];
  var maxFreq := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    var x := a_list[idx];
    var newcount := (if x in counts then counts[x] else 0) + 1;
    counts := counts[x := newcount];
    if newcount > maxFreq { maxFreq := newcount; }
    idx := idx + 1;
  }
  output := IntToString(n - maxFreq);
}

