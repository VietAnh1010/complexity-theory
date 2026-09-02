// 1244_A. Pens and Pencils  (problem 89, solution 89_909)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = input()
// n = int(n)
// for i in range(0,n):
//     l= input()
//     a,b,c,d,k = l.split()
//     a= int(a)
//     b= int(b)
//     c= int(c)
//     d= int(d)
//     k= int(k)
//     if (a%c!=0):
//         pens = int(a/c) + 1
//     else:
//         pens = int(a/c)
//     if (b%d!=0):
//         pins = int(b/d) + 1
//     else:
//         pins = int(b/d)
//     if ((pins+pens)>k):
//         print(-1)
//     else:
//         print(pens,pins)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |lists| == n
  requires forall idx :: 0 <= idx < |lists| ==>
    |lists[idx]| >= 5 && lists[idx][2] != 0 && lists[idx][3] != 0
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var l := lists[i];
    var a := l[0];
    var b := l[1];
    var c := l[2];
    var d := l[3];
    var k := l[4];
    var pens := if a % c == 0 then a / c else a / c + 1;
    var pins := if b % d == 0 then b / d else b / d + 1;
    if pins + pens > k {
      parts := parts + ["-1"];
    } else {
      parts := parts + [IntToString(pens) + " " + IntToString(pins)];
    }
    i := i + 1;
  }
  output := Join(parts, "\n");
}
