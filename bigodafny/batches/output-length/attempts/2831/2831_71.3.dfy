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

include "../../../../prelude.dfy"
import opened Prelude

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma SndRange(pairs: seq<(int,int)>, sorted: seq<(int,int)>, a: seq<(int,int)>, a0: int, n: int)
  requires n >= 1
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k].1 <= n
  requires forall x :: x in sorted <==> x in pairs
  requires a == [(a0, 1)] + sorted
  ensures forall k :: 0 <= k < |a| ==> 1 <= a[k].1 <= n
{
  forall k | 0 <= k < |a| ensures 1 <= a[k].1 <= n {
    if k > 0 {
      assert a[k] == sorted[k - 1];
      assert sorted[k - 1] in sorted;
      assert sorted[k - 1] in pairs;
      var j :| 0 <= j < |pairs| && pairs[j] == sorted[k - 1];
    }
  }
}

lemma MulStep(x: nat, w: nat)
  ensures x * (w + 1) == x * w + x
{ }

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 10 * n + 2 * n * Digits(n) + |output| + 20
{
  var pairs: seq<(int,int)> := [];
  var i := 1;
  steps := 1;
  ghost var base0 := steps;
  ghost var D := Digits(n);
  ghost var K := 4 + 2 * D;
  while i < n
    invariant 1 <= i <= n
    invariant |pairs| == i - 1
    invariant steps <= base0 + 2 * (i - 1)
    invariant forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k].1 <= n
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
  SortKeepsElems(pairs, (x: (int,int), y: (int,int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  steps := steps + SortCost(n - 1);
  var a := [(a_list[0], 1)] + sorted;
  SndRange(pairs, sorted, a, a_list[0], n);
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
    invariant steps <= base1 + 3 * r + K * w
    decreases n - r, if broke then 0 else 1
  {
    var cur := a[r];
    if r == w {
      broke := true;
    } else {
      ghost var wbase := w;
      while w != n && cur.0 > 0
        invariant 0 <= w <= n
        invariant cur.1 == a[r].1
        invariant steps <= base1 + 3 * r + K * w
        decreases n - w
      {
        DigitsMono(cur.1, n);
        DigitsMono(a[w].1, n);
        ans := ans + [IntToString(cur.1) + " " + IntToString(a[w].1)];
        cur := (cur.0 - 1, cur.1);
        w := w + 1;
        steps := steps + 4 + Digits(cur.1) + Digits(a[w - 1].1);
        MulStep(K, w - 1);
      }
      r := r + 1;
      steps := steps + 3;
    }
  }
  MulMonoRight(K, w, n);
  assert K * n == 4 * n + 2 * n * D;
  if broke {
    output := "-1\n";
  } else {
    output := IntToString(|ans|) + "\n" + Join(ans, "\n") + "\n";
  }
  steps := steps + |output| + 5;
}
