// 918_A. Eleven  (problem 1699, solution 1699_98)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// n=int(input())
// l=[1,1]
// b=""
// for i in range(2,n+1):
// 	l.append(l[i-2]+l[i-1])
// for j in range(1,n+1):
// 	if j in l:
// 		b+="O"
// 	else:
// 		b+="o"
// print(b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var l := [1, 1];
  var i := 2;
  while i <= n
    decreases n - i + 1
  {
    l := l + [l[i - 2] + l[i - 1]];
    i := i + 1;
  }
  var parts: seq<string> := [];
  var j := 1;
  while j <= n
    decreases n - j + 1
  {
    var found := false;
    var k := 0;
    while k < |l|
      decreases |l| - k
    {
      if l[k] == j {
        found := true;
      }
      k := k + 1;
    }
    if found {
      parts := parts + ["O"];
    } else {
      parts := parts + ["o"];
    }
    j := j + 1;
  }
  output := Join(parts, "");
}
