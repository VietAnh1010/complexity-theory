// 769_B. News About Credit  (problem 2831, solution 2831_71)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import itertools
//
// n = int(input())
// a = list(map(int, input().split()))
// a = [(a[0], 1)] + sorted(zip(a[1:], itertools.count(2)), reverse=True)
// w = 1
// ans = [ ]
// for r, cur in enumerate(a):
//     if r == w:
//         print(-1)
//         break
//     while w != n and cur[0] > 0:
//         ans.append("%s %s" % (cur[1], a[w][1]))
//         cur = (cur[0] - 1, cur[1])
//         w += 1
// else:
//     print(len(ans))
//     print('\n'.join(ans))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 10 * n + |output| + 20
{
  var pairs: seq<(int,int)> := [];
  var i := 1;
  steps := 1;
  ghost var base0 := steps;
  while i < n
    invariant 1 <= i <= n
    invariant |pairs| == i - 1
    invariant steps <= base0 + 2 * (i - 1)
    decreases n - i
  {
    pairs := pairs + [(a_list[i], i + 1)];
    i := i + 1;
    steps := steps + 2;
  }
  SortCostTreeBound(n - 1);
  CeilLog2Monotone(n - 1, n);
  MulMonoRight(2 * (n - 1), CeilLog2(n - 1) + 1, CeilLog2(n) + 1);
  assert 2 * (n - 1) * (CeilLog2(n - 1) + 1) <= 2 * (n - 1) * (CeilLog2(n) + 1);
  MulMonoRight(CeilLog2(n) + 1, 2 * (n - 1), 2 * n);
  assert 2 * (n - 1) * (CeilLog2(n) + 1) <= 2 * n * (CeilLog2(n) + 1);
  assert SortCost(n - 1) <= 2 * n * (CeilLog2(n) + 1) + 1;
  var sorted := Sort(pairs, (x: (int,int), y: (int,int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  steps := steps + SortCost(n - 1);
  var a := [(a_list[0], 1)] + sorted;
  var w := 1;
  var ans: seq<string> := [];
  var r := 0;
  var broke := false;
  ghost var base1 := steps;
  // The inner loop only advances w, and w never resets or decreases, so the
  // total number of inner-loop iterations across every outer iteration is
  // bounded by n (w starts at 1 and stops once it reaches n).
  while r < n && !broke
    invariant 0 <= r <= n
    invariant 0 <= w <= n
    invariant |a| == n
    invariant steps <= base1 + 3 * r + 4 * w
    decreases n - r, if broke then 0 else 1
  {
    var cur := a[r];
    if r == w {
      broke := true;
    } else {
      ghost var wbase := w;
      while w != n && cur.0 > 0
        invariant 0 <= w <= n
        invariant steps <= base1 + 3 * r + 4 * w
        decreases n - w
      {
        ans := ans + [IntToString(cur.1) + " " + IntToString(a[w].1)];
        cur := (cur.0 - 1, cur.1);
        w := w + 1;
        steps := steps + 4;
      }
      r := r + 1;
      steps := steps + 3;
    }
  }
  if broke {
    output := "-1\n";
  } else {
    output := IntToString(|ans|) + "\n" + Join(ans, "\n") + "\n";
  }
  steps := steps + |output| + 5;
}
