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

// Number of 1-entries in s[..k]: matches the count of taxi drivers seen so
// far. The problem guarantees exactly `m` (== b) drivers among the n+m
// residents, i.e. CountOnesUpTo(d_list, |d_list|) == b.
function CountOnesUpTo(s: seq<int>, k: nat): nat
  requires k <= |s|
  decreases k
{
  if k == 0 then 0 else CountOnesUpTo(s, k - 1) + (if s[k - 1] == 1 then 1 else 0)
}

lemma CountOnesMonotonic(s: seq<int>, i: nat, k: nat)
  requires i <= k <= |s|
  ensures CountOnesUpTo(s, i) <= CountOnesUpTo(s, k)
  decreases k - i
{
  if i < k {
    CountOnesMonotonic(s, i, k - 1);
  }
}

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
  requires b >= 1
  requires |d_list| == |c_list|
  requires CountOnesUpTo(d_list, |d_list|) == b
{
  var f: seq<int> := [];
  var j := 0;
  while j < |c_list|
    invariant 0 <= j <= |c_list|
    invariant |f| == CountOnesUpTo(d_list, j)
    decreases |c_list| - j
  {
    if d_list[j] == 1 {
      f := f + [c_list[j]];
    }
    j := j + 1;
  }

  var dArr: seq<int> := seq(b, i => 0);
  var q2 := 0;
  var hasQ2 := false;
  var q1 := 0;
  var hasQ1 := false;
  var q3 := -1;
  var q4 := 0;
  var idx := 0;
  while idx < |c_list|
    invariant 0 <= idx <= |c_list|
    invariant |dArr| == b
    invariant q4 == CountOnesUpTo(d_list, idx)
    invariant q3 == q4 - 1
    invariant hasQ2 == (q4 >= 1)
    invariant hasQ1 == (hasQ2 && q4 < |f|)
    invariant |f| == CountOnesUpTo(d_list, |c_list|)
    invariant q4 <= |f|
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
        dArr := dArr[q4 := dArr[q4] + 1];
      } else if !hasQ1 {
        dArr := dArr[q3 := dArr[q3] + 1];
      } else {
        if c_list[idx] - q2 <= q1 - c_list[idx] {
          dArr := dArr[q3 := dArr[q3] + 1];
        } else {
          dArr := dArr[q4 := dArr[q4] + 1];
        }
      }
    }
    idx := idx + 1;
    CountOnesMonotonic(d_list, idx, |c_list|);
  }
  output := JoinInts(dArr, " ");
}
