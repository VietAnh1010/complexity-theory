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

// Sort's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence,
// bounded O(k log k) -- precedent solutions-proved/1563/1563_497.dfy.
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { }
  else if m <= 1 { }
  else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

lemma SortCostNLogN(k: nat)
  ensures SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1
  decreases k
{
  if k <= 1 { return; }
  var a := k / 2;
  var b := k - k / 2;
  var L := CeilLog2(k);
  assert a + b == k;
  assert b == (k + 1) / 2;
  assert a <= b;
  SortCostNLogN(a);
  SortCostNLogN(b);
  CeilLog2Monotone(a, b);
  assert L == 1 + CeilLog2(b);
  assert CeilLog2(a) + 1 <= L;
  assert CeilLog2(b) + 1 == L;
  MulMonoRight(2 * a, CeilLog2(a) + 1, L);
  MulMonoRight(2 * b, CeilLog2(b) + 1, L);
  assert SortCost(a) <= 2 * a * L + 1;
  assert SortCost(b) <= 2 * b * L + 1;
  MulDistrib(2 * a, 2 * b, 2 * k, L);
  assert 2 * a * L + 2 * b * L == 2 * k * L;
  assert SortCost(k) == SortCost(a) + SortCost(b) + k;
  assert SortCost(k) <= 2 * k * L + k + 2;
  assert 2 * k * (L + 1) == 2 * k * L + 2 * k;
  assert k + 2 <= 2 * k + 1;
}

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
  SortCostNLogN(n - 1);
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
