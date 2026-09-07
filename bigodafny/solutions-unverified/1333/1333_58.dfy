// 1029_C. Maximal Intersection  (problem 1333, solution 1333_58)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l, r = [], []
// a, b = 0, 0
// for i in range(n):
//     a, b = map(int, input().split())
//     l.append(a)
//     r.append(b)
// minr = 10**10
// maxl = -1
// l1 = -1
// r1 = -1
// for i in range(n):
//     if l[i] > maxl:
//         maxl = l[i]
//         l1 = i
//     if r[i] < minr:
//         minr = r[i]
//         r1 = i
// l_1 = l.copy()
// l_2 = l.copy()
// r_1 = r.copy()
// r_2 = r.copy()
// l_1.pop(l1)
// r_1.pop(l1)
// l_2.pop(r1)
// r_2.pop(r1)
// print(max(0, min(r_1)-max(l_1), min(r_2)-max(l_2)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string)
  requires n >= 2
  requires n == |intervals|
  requires forall k :: 0 <= k < n ==> |intervals[k]| >= 2
  requires forall k :: 0 <= k < n ==> intervals[k][1] < 10000000000
  requires exists k :: 0 <= k < n && intervals[k][0] > -1
{
{

  var l := seq(n, idx requires 0 <= idx < n => intervals[idx][0]);
  var r := seq(n, idx requires 0 <= idx < n => intervals[idx][1]);
  var maxl := -1;
  var l1 := -1;
  var minr := 10000000000;
  var r1 := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant l1 == -1 ==> maxl == -1
    invariant l1 == -1 ==> forall k :: 0 <= k < i ==> l[k] <= -1
    invariant l1 != -1 ==> 0 <= l1 < i
    invariant r1 == -1 ==> minr == 10000000000
    invariant r1 == -1 ==> forall k :: 0 <= k < i ==> r[k] >= minr
    invariant r1 != -1 ==> 0 <= r1 < i
    decreases n - i
  {
    if l[i] > maxl { maxl := l[i]; l1 := i; }
    if r[i] < minr { minr := r[i]; r1 := i; }
    i := i + 1;
  }
  assert forall k :: 0 <= k < n ==> l[k] == intervals[k][0];
  assert forall k :: 0 <= k < n ==> r[k] == intervals[k][1];
  assert l1 != -1;
  assert r1 != -1;
  var l_1 := l[..l1] + l[l1+1..];
  var r_1 := r[..l1] + r[l1+1..];
  var l_2 := l[..r1] + l[r1+1..];
  var r_2 := r[..r1] + r[r1+1..];
  var opt1 := MinSeq(r_1) - MaxSeq(l_1);
  var opt2 := MinSeq(r_2) - MaxSeq(l_2);
  var best := if opt1 > opt2 then opt1 else opt2;
  var ans := if best > 0 then best else 0;
  output := IntToString(ans);
}
}
