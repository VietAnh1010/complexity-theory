// 350_A. TL  (problem 305, solution 305_284)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// string = input()
// numbers = string.split()
// a = int(numbers[0])
// b = int(numbers[1])
// string = input()
// right = list(map(int, string.split()))
// string = input()
// wrong = list(map(int, string.split()))
// p = max(right)
// q = min(wrong)
// r = min(right)
// for x in range(p, q):
//     if r * 2 <= x:
//         print(x)
//         break
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// MaxSeq/MinSeq are pure recursive prelude functions -- each charged its
// argument's length (COMPLEXITY.md: recursive prelude function over a seq).
method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |c_list| > 0
  requires |d_list| > 0
  ensures steps <= 2 * |c_list| + |d_list| + 4
{
  var p := MaxSeq(c_list);
  var q := MinSeq(d_list);
  var r := MinSeq(c_list);
  steps := |c_list| + |d_list| + |c_list| + 1;
  var threshold := if p >= 2 * r then p else 2 * r;
  output := if threshold < q then IntToString(threshold) else "-1";
  steps := steps + 3;
}
