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

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 5 * NLogN(n) + 40 * n + 14 + 2 * |output|
{
  steps := 0;
  var pairs: seq<(int, int)> := [];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |pairs| == i - 1
    invariant steps == 8 * (i - 1)
    invariant forall k :: 0 <= k < |pairs| ==> 2 <= pairs[k].1 <= n
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + (4 + |[(a_list[i], i + 1)]|);
    pairs := pairs + [(a_list[i], i + 1)];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  SortCostWithin(|pairs|, n);
  steps := steps + SortCost(|pairs|);
  var sorted := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  steps := steps + (3 + |sorted|);
  var a := [(a_list[0], 1)] + sorted;
  SortKeepsElems(pairs, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  assert forall k :: 0 <= k < n ==> 1 <= a[k].1 <= n by {
    forall k | 0 <= k < n ensures 1 <= a[k].1 <= n {
      if k > 0 {
        assert a[k] == sorted[k - 1];
        assert sorted[k - 1] in sorted;
      }
    }
  }
  ghost var B := steps;
  ghost var K: nat := 19 + 3 * CeilLog2(n);
  var w := 1;
  var ans: seq<string> := [];
  var r := 0;
  var broke := false;
  while r < n && !broke
    invariant 0 <= r <= n
    invariant 0 <= w <= n
    invariant |a| == n
    invariant 1 <= w
    invariant forall k :: 0 <= k < n ==> 1 <= a[k].1 <= n
    invariant steps <= B + 12 * r + (w - 1) * K + (if broke then 6 else 0)
    decreases n - r, if broke then 0 else 1
  {
    steps := steps + (3 + if r < n then 1 else 0);
    steps := steps + 1;
    var cur := a[r];
    steps := steps + 1;
    if r == w {
      broke := true;
    } else {
      while w != n && cur.0 > 0
        invariant 0 <= w <= n
        invariant 1 <= w
        invariant 1 <= cur.1 <= n
        invariant steps <= B + 12 * r + 6 + (w - 1) * K
        decreases n - w
      {
        IntToStringDigits(a[w].1);
        DigitsBoundN(cur.1, n);
        DigitsBoundN(a[w].1, n);
        steps := steps + (3 + if w != n then 2 else 0);
        steps := steps + (4 + Digits(cur.1) + |" "| + Digits(a[w].1) + |IntToString(a[w].1)| + |[IntToString(cur.1) + " " + IntToString(a[w].1)]|);
        ans := ans + [IntToString(cur.1) + " " + IntToString(a[w].1)];
        steps := steps + 4;
        cur := (cur.0 - 1, cur.1);
        steps := steps + 1;
        CostMulDistrib(w - 1, 1, w, K);
        w := w + 1;
      }
      steps := steps + (2 + if w != n then 2 else 0);
      steps := steps + 1;
      r := r + 1;
    }
  }
  CostMulMonoLeft(w - 1, n, K);
  FinalMul(n, K);
  steps := steps + (2 + if r < n then 1 else 0);
  if broke {
    output := "-1\n";
  } else {
    IntToStringDigits(|ans|);
    if |ans| >= 1 { JoinLen(ans, "\n"); }
    steps := steps + (1 + Digits(|ans|) + |"\n"| + (SumLen(ans) + |ans|) + |Join(ans, "\n")| + |"\n"|);
    output := IntToString(|ans|) + "\n" + Join(ans, "\n") + "\n";
  }
}

import opened Prelude

lemma DigitsLog(x: nat)
  requires x >= 1
  ensures Digits(x) <= CeilLog2(x) + 1
  decreases x
{
  if x >= 10 {
    DigitsLog(x / 10);
    CeilLog2Monotone(x / 10, (x + 1) / 2);
  }
}

lemma DigitsBoundN(x: nat, n: nat)
  requires 1 <= x <= n
  ensures Digits(x) <= CeilLog2(n) + 1
{
  DigitsLog(x);
  CeilLog2Monotone(x, n);
}

lemma FinalMul(n: nat, K: nat)
  requires K == 19 + 3 * CeilLog2(n)
  ensures n * K <= 3 * NLogN(n) + 16 * n
{
  reveal NLogN();
  assert n * K == 16 * n + 3 * (n * (CeilLog2(n) + 1));
}
