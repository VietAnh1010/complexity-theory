// 1445_B. Elimination  (problem 914, solution 914_416)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// import math
// import collections
// input=sys.stdin.readline
// t=int(input())
// for w in range(t):
//     a,b,c,d=(int(i) for i in input().split())
//     print(max(a+b,c+d))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| == 4
  ensures steps <= 11 * |matrix| + 2 * |output| + 2
{
  steps := 1;
  output := "";
  var i := 0;
  while i < |matrix|
    invariant 0 <= i <= |matrix|
    invariant steps <= 1 + 11 * i + 2 * |output|
    decreases |matrix| - i
  {
    var row := matrix[i];
    var a := row[0] + row[1];
    var b := row[2] + row[3];
    var mx := if a > b then a else b;
    IntToStringDigits(mx);
    steps := steps + 11 + 2 * |IntToString(mx)| + 1;
    output := output + IntToString(mx) + "\n";
    i := i + 1;
  }
}
