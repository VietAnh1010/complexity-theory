// 1187_A. Stickers and Toys  (problem 1231, solution 1231_51)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for i in range(t):
//     l=list(map(int,input().split()))
//     print(max(l[0]-l[1],l[0]-l[2])+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var l := a_list[i];
    var v1 := l[0] - l[1];
    var v2 := l[0] - l[2];
    var m := if v1 > v2 then v1 else v2;
    lines := lines + [IntToString(m + 1)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
