// 614_A. Link/Cut Tree  (problem 1972, solution 1972_295)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/usr/local/bin/python3
// 
// import sys
// 
// l, r, k = map(int, input().split())
// res = 1
// if k == 1: 
// 	if l == 1:
// 		print(1)
// 	else:
// 		print(-1)
// 	sys.exit()
// ans = 0
// while (res < l):
// 	res *= k;
// while (res <= r):
// 	print(res)
// 	ans += 1
// 	res *= k
// if ans == 0:
// 	print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
  decreases *
{
  var l := a;
  var r := b;
  var k := c;
  if k == 1 {
    if l == 1 {
      output := "1";
    } else {
      output := "-1";
    }
    return;
  }
  var res := 1;
  while res < l
    decreases *
  {
    res := res * k;
  }
  var lines: seq<string> := [];
  var ans := 0;
  while res <= r
    decreases *
  {
    lines := lines + [IntToString(res)];
    ans := ans + 1;
    res := res * k;
  }
  if ans == 0 {
    output := "-1";
  } else {
    output := Join(lines, "\n");
  }
}
