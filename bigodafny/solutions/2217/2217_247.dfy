// 501_B. Misha and Changing Handles  (problem 2217, solution 2217_247)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q = int(input())
// n = [input() for x in range(q)]
// a = [n[0].split(), ]
// for x in range(1, q):
//     f = False
//     s = n[x].split()
//     for y in a:
//         if s[0] == y[-1]:
//             y.append(s[1])
//             f = True
//             break
//     if not f:
//         a.append(s)
// print(len(a))
// for x in a:
//     print(x[0], x[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, handles: seq<string>) returns (output: string)
  // every line is "old new": two whitespace-separated tokens
  requires 1 <= n <= |handles|
  requires forall k :: 0 <= k < |handles| ==> |SplitWs(handles[k])| >= 2
{
  var first := SplitWs(handles[0]);
  var chains: seq<seq<string>> := [ [first[0], first[1]] ];
  var x := 1;
  while x < n
    invariant 0 <= x
    invariant forall y :: 0 <= y < |chains| ==> |chains[y]| >= 2
    decreases n - x
  {
    var s := SplitWs(handles[x]);
    var f := false;
    var y := 0;
    while y < |chains| && !f
      invariant 0 <= y <= |chains|
      invariant forall z :: 0 <= z < |chains| ==> |chains[z]| >= 2
      decreases |chains| - y
    {
      var chain := chains[y];
      if s[0] == chain[|chain|-1] {
        chains := chains[y := chain + [s[1]]];
        f := true;
      }
      y := y + 1;
    }
    if !f {
      chains := chains + [ [s[0], s[1]] ];
    }
    x := x + 1;
  }
  var lines: seq<string> := [IntToString(|chains|)];
  var k := 0;
  while k < |chains|
    invariant 0 <= k <= |chains|
    invariant forall y :: 0 <= y < |chains| ==> |chains[y]| >= 2
    decreases |chains| - k
  {
    var chain := chains[k];
    lines := lines + [chain[0] + " " + chain[|chain|-1]];
    k := k + 1;
  }
  output := Join(lines, "\n");
}
