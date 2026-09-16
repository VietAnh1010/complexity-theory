// 1337_A. Ichihime and Triangle  (problem 2325, solution 2325_862)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
//     l=list(map(int,input().split()))
//     a,b,c,d=l[0],l[1],l[2],l[3]
//     x=b
//     y=c
//     z=c
//     print(x,y,z)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var l := lists[i];
    var a := l[0];
    var b := l[1];
    var c := l[2];
    var d := l[3];
    var x := b;
    var y := c;
    var z := c;
    parts := parts + [IntToString(x) + " " + IntToString(y) + " " + IntToString(z)];
    i := i + 1;
  }
  output := Join(parts, "\n");
}
