// 1372_B. Omkar and Last Class of Math  (problem 1234, solution 1234_71)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// 
// def solve(n):
//     p = 1
//     for i in range(2, int(math.ceil(math.sqrt(n)))+1):
//         if n % i == 0:
//             p = i
//             break
//     if p != 1:
//         k = n//p
//     else:
//         k = 1
//     return " ".join([str(k), str(n - k)])
// 
// 
// def read():
//     t = int(input())
//     for i in range(t):
//         n = int(input())
//         ans = solve(n)
//         print(ans)
// 
// read()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string)
{
  var lines: seq<string> := [];
  var t := 0;
  while t < N
    decreases N - t
  {
    var n := numbers[t];
    var p := 1;
    var limit := 1;
    while limit * limit < n
      decreases n - limit * limit
    {
      limit := limit + 1;
    }
    var i := 2;
    var found := false;
    while i <= limit && !found
      decreases limit - i
    {
      if n % i == 0 {
        p := i;
        found := true;
      }
      i := i + 1;
    }
    var k := if p != 1 then FloorDiv(n, p) else 1;
    lines := lines + [IntToString(k) + " " + IntToString(n - k)];
    t := t + 1;
  }
  output := Join(lines, "\n");
}
