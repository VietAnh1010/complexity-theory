// p02293 Parallel/Orthogonal  (problem 2183, solution 2183_2)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=int(input())
//
// for _ in [0]*q:
//     x0,y0,x1,y1,x2,y2,x3,y3=map(int,input().split())
//     a1=x1-x0
//     a2=x3-x2
//     b1=y1-y0
//     b2=y3-y2
//     parallel=a1*b2-a2*b1
//     orthogonal=a1*a2+b1*b2
//     if parallel==0:
//         print("2")
//     elif orthogonal==0:
//         print("1")
//     else:
//         print("0")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// IntToString(x) and |IntToString(x)| are each charged 1 (COMPLEXITY.md convention:
// digit strings here are single-character, "0"/"1"/"2").
ghost function SumLen2183(parts: seq<string>): nat
  decreases |parts|
{
  if |parts| == 0 then 0 else |parts[0]| + SumLen2183(parts[1..])
}

lemma SumLenBound2183(parts: seq<string>, B: nat)
  requires forall k :: 0 <= k < |parts| ==> |parts[k]| <= B
  ensures SumLen2183(parts) <= B * |parts|
  decreases |parts|
{
  if |parts| > 0 {
    SumLenBound2183(parts[1..], B);
  }
}

method Solve(n: int, rows: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |rows| == n
  requires forall k :: 0 <= k < n ==> |rows[k]| >= 8
  ensures steps <= 22 * n + 6
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |lines| == i
    invariant forall k :: 0 <= k < |lines| ==> |lines[k]| == 1
    invariant steps <= 20 * i + 1
    decreases n - i
  {
    var row := rows[i];
    var x0 := row[0]; var y0 := row[1]; var x1 := row[2]; var y1 := row[3];
    var x2 := row[4]; var y2 := row[5]; var x3 := row[6]; var y3 := row[7];
    var a1 := x1 - x0;
    var a2 := x3 - x2;
    var b1 := y1 - y0;
    var b2 := y3 - y2;
    var parallel := a1 * b2 - a2 * b1;
    var orthogonal := a1 * a2 + b1 * b2;
    var res := if parallel == 0 then 2 else if orthogonal == 0 then 1 else 0;
    var resStr := IntToString(res);
    lines := lines + [resStr];
    i := i + 1;
    steps := steps + 20;
  }
  assert forall k :: 0 <= k < |lines| ==> |lines[k]| <= 1;
  SumLenBound2183(lines, 1);
  output := Join(lines, "\n");
  steps := steps + SumLen2183(lines) + |lines|;
}
