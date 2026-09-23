// p03346 AtCoder Grand Contest 024 - Backfront  (problem 785, solution 785_75)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N = int(input())
// P = [int(input()) for i in range(N)]
//
//
// Q = sorted([(p, i) for i, p in enumerate(P, start=1)])
// Q = [i for p, i in Q]
//
// dp = [1] * (N + 1)
// for i in range(1, N):
//     if Q[i] > Q[i - 1]:
//         dp[i] = dp[i - 1] + 1
//
// print(N - max(dp))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Sort's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence,
// bounded O(k log k) -- precedent solutions-proved/2071/2071_39.dfy. Both
// `seq(len, f)` comprehensions stand in for the Python's O(n) list builds
// and are charged their length, one unit per element, matching them.
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

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |numbers| == n
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 12 * n + 10
{
  var pairs := seq(|numbers|, i requires 0 <= i < |numbers| => (numbers[i], i+1));
  steps := 1 + |numbers|;
  var srt := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  SortCostNLogN(|pairs|);
  steps := steps + SortCost(|pairs|);
  var q := seq(|srt|, i requires 0 <= i < |srt| => srt[i].1);
  steps := steps + |srt|;
  assert |q| == n;
  var dp := seq(n+1, _ => 1);
  steps := steps + n + 1;
  var i := 1;
  ghost var b1 := steps;
  while i < n
    invariant 1 <= i <= n
    invariant |dp| == n + 1
    invariant steps <= b1 + 3 * (i - 1)
    decreases n - i
  {
    if q[i] > q[i-1] {
      dp := dp[i := dp[i-1] + 1];
    }
    i := i + 1;
    steps := steps + 3;
  }
  var mx := dp[0];
  steps := steps + 1;
  i := 1;
  ghost var b2 := steps;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |dp| == n + 1
    invariant steps <= b2 + 2 * (i - 1)
    decreases n - i
  {
    if dp[i] > mx { mx := dp[i]; }
    i := i + 1;
    steps := steps + 2;
  }
  output := IntToString(n - mx);
  steps := steps + 1;
}
