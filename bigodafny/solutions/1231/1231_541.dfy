// 1187_A. Stickers and Toys  (problem 1231, solution 1231_541)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// T=int(input())
// for t in range(0,T):
//     n,s,t=map(int,input().split())
//     print(max(n-s+1,n-t+1))
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
    var row := a_list[i];
    var nv := row[0];
    var sv := row[1];
    var tv := row[2];
    var v1 := nv - sv + 1;
    var v2 := nv - tv + 1;
    var m := if v1 > v2 then v1 else v2;
    lines := lines + [IntToString(m)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
