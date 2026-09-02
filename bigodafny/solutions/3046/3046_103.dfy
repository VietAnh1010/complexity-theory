// 595_A. Vitaly and Night  (problem 3046, solution 3046_103)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// 
// ans = 0
// for _ in range(n):
// 	windows = list(map(int, input().split()))
// 	ans += sum(min(1, windows[i] + windows[i + 1]) for i in range(0, m * 2, 2))
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, v_3: seq<seq<int>>) returns (output: string)
{
  var ans := 0;
  var r := 0;
  while r < |v_3|
    invariant 0 <= r <= |v_3|
    decreases |v_3| - r
  {
    var windows := v_3[r];
    var i := 0;
    while i < 2 * m
      invariant 0 <= i
      decreases 2 * m - i
    {
      if i + 1 < |windows| {
        var s := windows[i] + windows[i + 1];
        ans := ans + (if s < 1 then s else 1);
      }
      i := i + 2;
    }
    r := r + 1;
  }
  output := IntToString(ans);
}
