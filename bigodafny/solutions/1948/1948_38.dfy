// 47_A. Triangular numbers  (problem 1948, solution 1948_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = int(input())
// n = 1
// 
// while 2*a>n**2+n:
// 	n +=1
// 
// if (2*a)-(n**2+n)==0:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  decreases *
{
  var a := n;
  var m := 1;
  while 2 * a > m * m + m
    decreases *
  {
    m := m + 1;
  }
  if 2 * a - (m * m + m) == 0 {
    output := "YES";
  } else {
    output := "NO";
  }
}
