// 389_A. Fox and Number Game  (problem 281, solution 281_138)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// x = list(sorted(map(int, input().split())))
// 
// 
// def gcd(a, b):
//     while b > 0:
//         a, b = b, a % b
//     return a
// 
// tgcd = x.pop(0)
// for i in x:
//     tgcd = gcd(tgcd, i)
// 
// print(tgcd * n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var xs := SortInts(a_list);
  var g := xs[0];
  var i := 1;
  while i < |xs|
    decreases |xs| - i
  {
    g := Gcd(g, xs[i]);
    i := i + 1;
  }
  output := IntToString(g * n);
}

function Gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases b
{
  if b == 0 then a else Gcd(b, a % b)
}
