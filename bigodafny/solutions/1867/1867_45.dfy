// 1202_D. Print a 1337-string...  (problem 1867, solution 1867_45)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// from math import floor, sqrt, log
// 
// q = int(input())
// for _ in range(q):
// 	#a = c = 1
// 	n = int(input())
// 	if n == 1:
// 		print("1337")
// 		continue
// 	x = 2
// 	while (x * (x - 1) // 2 < n):
// 		x += 1
// 	x -= 1
// 	n -= x * (x - 1) // 2
// 	print("133", end = '')
// 	print('7' * n, end = '')
// 	print('3' * (x - 2), end = '')
// 	print('7')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  requires n >= 0
  requires |numbers| >= n
{
  var lines: seq<string> := [];
  var qi := 0;
  while qi < n
    invariant 0 <= qi <= n
    decreases n - qi
  {
    var val := numbers[qi];
    if val == 1 {
      lines := lines + ["1337"];
    } else {
      var x := 2;
      while x * (x - 1) / 2 < val
        decreases val - x * (x - 1) / 2
      {
        x := x + 1;
      }
      x := x - 1;
      var rem := val - x * (x - 1) / 2;
      var remN := if rem < 0 then 0 else rem;
      var threes := x - 2;
      var threesN := if threes < 0 then 0 else threes;
      var ans := "133" + Repeat("7", remN) + Repeat("3", threesN) + "7";
      lines := lines + [ans];
    }
    qi := qi + 1;
  }
  output := Join(lines, "\n");
}
