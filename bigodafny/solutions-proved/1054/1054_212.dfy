// 651_B. Beautiful Paintings  (problem 1054, solution 1054_212)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// from collections import Counter
// input = sys.stdin.readline
// 
// n = int(input())
// a = dict(Counter(sorted(input().split())))
// 
// ans = 0
// f = 0
// for val in a:
//     ans += min(f, a[val])
//     f += max(a[val] - f, 0)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 9 * |a_list| + 2 + |output|
{
  steps := 0;
  var counts: map<int, int> := map[];
  var maxFreq := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps <= 9 * idx
    decreases |a_list| - idx
  {
    steps := steps + 9;
    var x := a_list[idx];
    var newcount := (if x in counts then counts[x] else 0) + 1;
    counts := counts[x := newcount];
    if newcount > maxFreq { maxFreq := newcount; }
    idx := idx + 1;
  }
  output := IntToString(n - maxFreq);
  IntToStringDigits(n - maxFreq);
  steps := steps + 1 + Digits(n - maxFreq);
}

