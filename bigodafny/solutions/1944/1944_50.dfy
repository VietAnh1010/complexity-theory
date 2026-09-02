// 1550_A. Find The Array  (problem 1944, solution 1944_50)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// t=int(input())
// for i in range(t):
//     print(math.ceil(math.sqrt(int(input()))))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Smallest r >= 0 with r*r >= x, i.e. ceil(sqrt(x)) over the integers.
// Binary search, so a large x costs log(x) and not sqrt(x).
method CeilSqrt(x: int) returns (r: int)
  requires x >= 0
  ensures r >= 0
{
  if x <= 1 { return x; }
  var hi := 1;
  while hi * hi < x
    decreases x - hi * hi
  {
    hi := hi * 2;
  }
  var lo := 0;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid >= x { hi := mid; } else { lo := mid + 1; }
  }
  return lo;
}

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |numbers|
    decreases |numbers| - i
  {
    var r := CeilSqrt(if numbers[i] >= 0 then numbers[i] else 0);
    parts := parts + [IntToString(r)];
    i := i + 1;
  }
  output := Join(parts, "\n") + "\n";
}
