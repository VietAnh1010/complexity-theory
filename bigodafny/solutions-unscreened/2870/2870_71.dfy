// 1463_A. Dungeon  (problem 2870, solution 2870_71)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// T = int(input())
// for i in range(0, T) :
//     a, b, c = input().split()
//     a = int(a)
//     b = int(b)
//     c = int(c)
//     Sum = a + b + c
//     if Sum % 9 == 0 and Sum / 9 <= min(a, min(b, c)) :
//         print("YES")
//     else :
//         print("NO")
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
    var sm := SumSeq(s);
    var mn := MinSeq(s);
    if sm % 9 == 0 && mn >= sm / 9 {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := if |lines| > 0 then Join(lines, "\n") + "\n" else "";
}
