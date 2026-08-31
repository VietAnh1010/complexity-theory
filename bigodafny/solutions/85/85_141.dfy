// 1075_B. Taxi drivers and Lyft  (problem 85, solution 85_141)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// a = list(map(int, input().split()))
// s = list(map(int, input().split()))
// d = [0]*m
// f = []
// for q in range(len(s)):
//     if s[q] == 1:
//         f.append(a[q])
// q2, q1 = -float('inf'), f[0]
// q3, q4 = -1, 0
// for q in range(len(a)):
//     if s[q] == 1:
//         q2, q1 = a[q], f[q4+1] if len(f) > q4+1 else float('inf')
//         q3, q4 = q3+1, q4+1
//     else:
//         if q2 == -float('inf'):
//             d[q4] += 1
//         elif q1 == float('inf'):
//             d[q3] += 1
//         else:
//             if a[q]-q2 <= q1-a[q]:
//                 d[q3] += 1
//             else:
//                 d[q4] += 1
// print(*d)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
{
  assume {:axiom} b >= 1;
  var f: seq<int> := [];
  var j := 0;
  while j < |c_list|
    decreases |c_list| - j
  {
    if d_list[j] == 1 {
      f := f + [c_list[j]];
    }
    j := j + 1;
  }
  assume {:axiom} |f| <= b;

  var dArr: seq<int> := seq(b, i => 0);
  var q2 := 0;
  var hasQ2 := false;
  var q1 := 0;
  var hasQ1 := false;
  var q3 := -1;
  var q4 := 0;
  var idx := 0;
  while idx < |c_list|
    decreases |c_list| - idx
  {
    if d_list[idx] == 1 {
      q2 := c_list[idx];
      hasQ2 := true;
      if q4 + 1 < |f| {
        q1 := f[q4 + 1];
        hasQ1 := true;
      } else {
        hasQ1 := false;
      }
      q3 := q3 + 1;
      q4 := q4 + 1;
    } else {
      if !hasQ2 {
        assume {:axiom} 0 <= q4 < |dArr|;
        dArr := dArr[q4 := dArr[q4] + 1];
      } else if !hasQ1 {
        assume {:axiom} 0 <= q3 < |dArr|;
        dArr := dArr[q3 := dArr[q3] + 1];
      } else {
        if c_list[idx] - q2 <= q1 - c_list[idx] {
          assume {:axiom} 0 <= q3 < |dArr|;
          dArr := dArr[q3 := dArr[q3] + 1];
        } else {
          assume {:axiom} 0 <= q4 < |dArr|;
          dArr := dArr[q4 := dArr[q4] + 1];
        }
      }
    }
    idx := idx + 1;
  }
  output := JoinInts(dArr, " ");
}
