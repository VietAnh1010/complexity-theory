// 432_A. Choosing Teams  (problem 2166, solution 2166_288)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int,input().split())
// y = map(int,input().split())
// z = sorted(y)
// k = 5-k
// if(k<0):
// 	print("0")
// else:
// 	count = 0
// 	for i in z:
// 		if(i<=k):
// 			count = count+1
// print(int(count/3))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(nlogn) -- agrees, on the sort alone. Sibling 2166_84 carries O(n)
// and does the same counting without sorting, so the two labels are
// consistent with each other and both are right: the rows differ.
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

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |numbers| * (CeilLog2(|numbers|) + 1) + 4 * |numbers| + 7
{
  SortCostNLogN(|numbers|);
  steps := 1 + SortCost(|numbers|);
  ghost var s0 := steps;
  var z := SortInts(numbers);
  var k2 := 5 - k;
  steps := steps + 2;
  if k2 < 0 {
    output := "0";
    steps := steps + 1;
  } else {
    var count := 0;
    var i := 0;
    while i < |z|
      invariant 0 <= i <= |z|
      invariant steps == s0 + 2 + 4 * i
      decreases |z| - i
    {
      if z[i] <= k2 { count := count + 1; }
      i := i + 1;
      steps := steps + 4;
    }
    output := IntToString(FloorDiv(count, 3));
    steps := steps + 3;
  }
}
