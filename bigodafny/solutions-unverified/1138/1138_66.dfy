// 499_A. Watching a movie  (problem 1138, solution 1138_66)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x=map(int, input().split())
// w=0
// m=1
// for i in range(n):
// 	l,r=map(int, input().split())
// 	k=r
// 	l,r=l-m,r-m
// 	w+=l%x+r-l+1
// 	m=k+1
// print(w)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, data: seq<seq<int>>) returns (output: string)
{
  var w := 0;
  var mm := 1;
  var i := 0;
  while i < n
    decreases n - i
  {
    var l := data[i][0];
    var r := data[i][1];
    var k := r;
    l := l - mm;
    r := r - mm;
    w := w + FloorMod(l, m) + (r - l + 1);
    mm := k + 1;
    i := i + 1;
  }
  output := IntToString(w);
}
