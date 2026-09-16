// 1463_A. Dungeon  (problem 2870, solution 2870_46)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// for i in range(n):
//     s = list(map(int, input().split()))
//     d = sum(s)
//     if min(s) >= d // 9 and d % 9 == 0:
//         print('YES')
//     else:
//         print('NO')
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
  requires |values_list| == n
  requires forall k :: 0 <= k < |values_list| ==> |values_list[k]| > 0
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    var s := values_list[i];
    var d := SumSeq(s);
    var m := MinSeq(s);
    if m >= d / 9 && d % 9 == 0 {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := if |lines| > 0 then Join(lines, "\n") + "\n" else "";
}
