// 1328_B. K-th Beautiful String  (problem 2819, solution 2819_926)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # Anuneet Anand 
// import math
// T = int(input())
// 
// while T:
// 	n,k = map(int,input().split())
// 	x = int(((1) + math.sqrt(1 + (8 * (k-1)))) / 2)
// 	d = int(math.floor((-1 + math.sqrt(1+ 8 * k - 8)) / 2)) 
// 	b = (d * (d + 1)) / 2 + 1 
// 	y = int(k - b)
// 	A = ['a' for i in range(n)]
// 	A[n-x-1]='b'
// 	A[n-y-1]='b'
// 	R = "a"*(n-x-1)+"b"+"a"*(x-y-1)+"b" + y*"a"
// 	print(R)
// 	T = T-1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method IntSqrtFloor(v: int) returns (r: int)
  requires v >= 0
{
  var lo := 0;
  var hi := v + 1;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid <= v {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  r := lo - 1;
}

function RepStr(s: string, n: int): string
  decreases if n > 0 then n else 0
{
  if n <= 0 then "" else s + RepStr(s, n - 1)
}

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
  {
    var row := pairs_list[t];
    if |row| >= 2 {
      var nn := row[0];
      var k := row[1];
      var val := 8 * k - 7;
      if val < 0 { val := 0; }
      var s := IntSqrtFloor(val);
      var x := FloorDiv(1 + s, 2);
      var d := FloorDiv(s - 1, 2);
      var b := FloorDiv(d * (d + 1), 2) + 1;
      var y := k - b;
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      results := results + [r];
    }
    t := t + 1;
  }
  output := Join(results, "\n");
}
