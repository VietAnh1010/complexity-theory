// 631_A. Interview  (problem 1029, solution 1029_92)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// ps = list(map(int, input().split()))
// qs = list(map(int, input().split()))
// 
// maxi = 0
// s_a, s_b = 0, 0
// for l in range(n):
//     s_a = ps[l]
//     s_b = qs[l]
//     for r in range(l, n):
//         s_a = s_a | ps[r]
//         s_b = s_b | qs[r]
//         maxi = max(maxi, s_a + s_b)
// 
// print(maxi)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function BitOr(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else 2 * BitOr(a / 2, b / 2) + (if a % 2 == 1 || b % 2 == 1 then 1 else 0)
}


method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var maxi := 0;
  var l := 0;
  while l < n
    decreases n - l
  {
    var sa := a_list[l];
    var sb := b_list[l];
    var r := l;
    while r < n
      decreases n - r
    {
      sa := BitOr(sa, a_list[r]);
      sb := BitOr(sb, b_list[r]);
      if sa + sb > maxi { maxi := sa + sb; }
      r := r + 1;
    }
    l := l + 1;
  }
  output := IntToString(maxi);
}
