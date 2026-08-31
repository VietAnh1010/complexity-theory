// 110_C. Lucky Sum of Digits  (problem 271, solution 271_51)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x,y=n//7,n%7
// z,w=y//4,y%4
// if(x<w):
//     print(-1)
// else:
//     print('4'*(z+w*2)+'7'*(x-w))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var x := n / 7;
  var y := n % 7;
  var z := y / 4;
  var w := y % 4;
  if x < w {
    output := "-1";
  } else {
    output := Repeat('4', z + w * 2) + Repeat('7', x - w);
  }
}

function Repeat(c: char, n: int): string
  decreases if n < 0 then 0 else n
{
  if n <= 0 then "" else [c] + Repeat(c, n - 1)
}
