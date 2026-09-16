// 1197_B. Pillars  (problem 1453, solution 1453_483)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// p=1
// r=1
// e=0
// if r==0:
//     print("NO")
// else:
//     k=max(a)
//     t=a.index(k)
//     c=max(t,n-t-1)
//     for i in range(c):
//         if i<t:
//             if a[i]<a[i+1]:
//                 pass
//             else:
//                 e=1
//                 break
//         if i+t<n-1:
//             if a[i+t]>a[i+1+t]:
//                 pass
//             else:
//                 e=1
//                 break
//     if e==1:
//         print("NO")
//     else:
//         print("YES")
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MaxSeqFromIn(s: seq<int>, i: nat, best: int)
  requires i <= |s|
  ensures MaxSeqFrom(s, i, best) == best || MaxSeqFrom(s, i, best) in s[i..]
  decreases |s| - i
{
  if i == |s| {
  } else {
    MaxSeqFromIn(s, i + 1, if s[i] > best then s[i] else best);
  }
}

lemma MaxSeqIn(s: seq<int>)
  requires |s| > 0
  ensures MaxSeq(s) in s
{
  MaxSeqFromIn(s, 1, s[0]);
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 9 * n + 10
{
  steps := 1;
  var k := MaxSeq(a_list);          // recursive prelude fn over a_list: charge |a_list|
  steps := steps + n;
  MaxSeqIn(a_list);
  var m :| 0 <= m < |a_list| && a_list[m] == k;
  var t := 0;
  while a_list[t] != k
    invariant 0 <= t <= m
    invariant steps <= n + 1 + 2 * t
    decreases m - t
  {
    t := t + 1;
    steps := steps + 2;
  }
  assert t <= m < n;
  var c := if t > n - t - 1 then t else n - t - 1;
  assert c <= n - 1;
  var e := 0;
  var i := 0;
  while i < c && e == 0
    invariant 0 <= i <= c
    invariant steps <= n + 1 + 2 * t + 1 + 6 * i
    decreases c - i
  {
    if i < t {
      if a_list[i] < a_list[i+1] {
      } else {
        e := 1;
      }
    }
    if e == 0 && i + t < n - 1 {
      if a_list[i+t] > a_list[i+1+t] {
      } else {
        e := 1;
      }
    }
    i := i + 1;
    steps := steps + 6;
  }
  output := if e == 1 then "NO" else "YES";
  steps := steps + 1;
  assert steps <= n + 1 + 2 * t + 1 + 6 * c + 1;
  assert t < n;
  assert c <= n - 1;
}
