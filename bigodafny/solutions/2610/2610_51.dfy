// 490_A. Team Olympiad  (problem 2610, solution 2610_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [[] for i in range(3)]
// for i, x in enumerate(map(int, input().split()), 1):
//         a[x-1] += [i]
// k = min(len(a[0]), len(a[1]), len(a[2]))
// print(k)
// for i in range(k):
//         print(a[0][i], a[1][i], a[2][i])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var a0: seq<int> := [];
  var a1: seq<int> := [];
  var a2: seq<int> := [];
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
  {
    var x := a_list[idx];
    if x == 1 { a0 := a0 + [idx + 1]; }
    else if x == 2 { a1 := a1 + [idx + 1]; }
    else if x == 3 { a2 := a2 + [idx + 1]; }
    idx := idx + 1;
  }
  var k := |a0|;
  if |a1| < k { k := |a1|; }
  if |a2| < k { k := |a2|; }
  var lines: seq<string> := [];
  var i := 0;
  while i < k
    invariant 0 <= i <= k <= |a0| && k <= |a1| && k <= |a2|
    invariant |lines| == i
  {
    lines := lines + [IntToString(a0[i]) + " " + IntToString(a1[i]) + " " + IntToString(a2[i])];
    i := i + 1;
  }
  output := IntToString(k) + "\n";
  if |lines| > 0 {
    output := output + Join(lines, "\n") + "\n";
  }
}
