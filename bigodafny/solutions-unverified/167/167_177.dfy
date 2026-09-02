// 1184_A1. Heidi Learns Hashing (Easy)  (problem 167, solution 167_177)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = int(input())
// x = math.floor(math.sqrt(n))
// p = 0
// for i in range(1, x):
// 	if (n-1-i**2-i)%(2*i) == 0 :
// 		print(i,  (n-1-i**2-i)//(2*i))
// 		p = 1
// 		break
// if not p:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var x := IntSqrtFloor(n);
  var p := 0;
  var result := "";
  var i := 1;
  while i < x && p == 0
    decreases x - i
  {
    var expr := n - 1 - i * i - i;
    if expr % (2 * i) == 0 {
      result := IntToString(i) + " " + IntToString(expr / (2 * i));
      p := 1;
    }
    i := i + 1;
  }
  if p == 0 {
    result := "NO";
  }
  output := result;
}

method IntSqrtFloor(x: int) returns (r: int)
  requires x >= 0
{
  var lo := 0;
  var hi := x + 1;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid <= x {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  r := lo - 1;
}
