// 276_A. Lunch Rush  (problem 2012, solution 2012_342)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int, input().split())
// s = set()
// for i in range(n):
//     a,b=map(int, input().split())
//     if b > k:
//         s.add(a-(b-k))
//     else:
//         s.add(a)        
// print(max(s))        
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, pairs: seq<seq<int>>) returns (output: string)
{
  var a0 := pairs[0][0];
  var b0 := pairs[0][1];
  var best := if b0 > k then a0 - (b0 - k) else a0;
  var i := 1;
  while i < |pairs|
    decreases |pairs| - i
  {
    var a := pairs[i][0];
    var b := pairs[i][1];
    var v := if b > k then a - (b - k) else a;
    if v > best {
      best := v;
    }
    i := i + 1;
  }
  output := IntToString(best);
}
