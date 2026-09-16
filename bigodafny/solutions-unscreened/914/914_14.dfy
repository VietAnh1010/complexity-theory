// 1445_B. Elimination  (problem 914, solution 914_14)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for j in range(t):
// 	m=list(map(int,input().split()))
// 	a=m[0]+m[1]
// 	b=m[2]+m[3]
// 	if a>b:
// 		print(a)
// 	else:
// 		print(b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  output := "";
  var i := 0;
  while i < |matrix|
    decreases |matrix| - i
  {
    var row := matrix[i];
    var a := row[0] + row[1];
    var b := row[2] + row[3];
    var mx := if a > b then a else b;
    output := output + IntToString(mx) + "\n";
    i := i + 1;
  }
}
