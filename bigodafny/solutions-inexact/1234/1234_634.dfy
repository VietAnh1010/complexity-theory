// 1372_B. Omkar and Last Class of Math  (problem 1234, solution 1234_634)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def factors(n):
//     i = 1
//     while i * i <= n:
//         if n % i == 0:
//             yield i
//             yield n // i
//         i += 1
// 
// for t in range(int(input())):
//     n = int(input())
//     s = sorted(list(factors(n)))[-2]
//     print(s, n - s)
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
    var found := false;
    var i := 2;
    while i * i <= n && !found
      decreases n - i
    {
      if n % i == 0 {
        p := i;
        found := true;
      }
      i := i + 1;
    }
    var s := if found then FloorDiv(n, p) else 1;
    lines := lines + [IntToString(s) + " " + IntToString(n - s)];
    t := t + 1;
  }
  output := Join(lines, "\n");
}
