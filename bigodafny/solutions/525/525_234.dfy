// 1131_B. Draw!  (problem 525, solution 525_234)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// count=1
// a,b=0,0
// for i in range(n):
//     c,d=map(int,input().split(' '))
//     if min(c,d)>=max(a,b):
//         if a!=b:
//             count+=min(c,d)-max(a,b)+1
//         else:
//             count+=min(c,d)-max(a,b)
//     a,b=c,d
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |points| == n
  requires forall k :: 0 <= k < |points| ==> |points[k]| >= 2
{
  var count := 1;
  var a := 0;
  var b := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var c := points[i][0];
    var d := points[i][1];
    var mn := if c < d then c else d;
    var mx := if a > b then a else b;
    if mn >= mx {
      if a != b {
        count := count + (mn - mx + 1);
      } else {
        count := count + (mn - mx);
      }
    }
    a := c;
    b := d;
    i := i + 1;
  }
  output := IntToString(count) + "\n";
}
