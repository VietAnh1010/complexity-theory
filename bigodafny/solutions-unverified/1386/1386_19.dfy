// 346_A. Alice and Bob  (problem 1386, solution 1386_19)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = int(input())
// arr = sorted(list(map(int, input().split())))
// b = 0
// for i in arr:
//     b = math.gcd(b, i)
// c = (arr[0] - 1) // b
// c += sum([(arr[i+1] - arr[i] - 1) // b for i in range(n-1)])
// print('Bob' if c % 2 == 0 else 'Alice')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b_list: seq<int>) returns (output: string)
{
  var n := a;
  var arr := SortInts(b_list);
  var g := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    g := Gcd(g, arr[i]);
    i := i + 1;
  }
  var c := FloorDiv(arr[0] - 1, g);
  i := 0;
  while i < n - 1
    decreases n - 1 - i
  {
    c := c + FloorDiv(arr[i+1] - arr[i] - 1, g);
    i := i + 1;
  }
  output := if FloorMod(c, 2) == 0 then "Bob" else "Alice";
}
