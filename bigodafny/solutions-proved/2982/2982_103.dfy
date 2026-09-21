// 1102_C. Doors Breaking and Repairing  (problem 2982, solution 2982_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,y=input().split()
// n=int(n)
// x=int(x)
// y=int(y)
//
// l=[int(x) for x in input().split()]
//
// l.sort()
//
// count_a=0
//
//
// for i in range(n):
// 	if(l[i]<=x):
// 		count_a+=1
//
// if(x>y):
// 	print(n)
//
// else:
// 	print((count_a%2)+(count_a//2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound (see
// solutions-proved/nlogn/603/603_284.dfy for the same argument) ----------

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

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires a >= 0
  ensures steps <= 2 * |d_list| * (CeilLog2(|d_list|) + 1) + 3 * a + 10
{
  steps := 1;
  var n := a;
  var x := b;
  var y := c;
  SortCostNLogN(|d_list|);
  steps := steps + SortCost(|d_list|);
  var l := SortInts(d_list);
  assert |l| == |d_list|;
  var countA := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + SortCost(|d_list|) + 3 * i
    decreases n - i
  {
    if i < |l| && l[i] <= x { countA := countA + 1; }
    i := i + 1;
    steps := steps + 3;
  }
  if x > y {
    output := IntToString(n);
  } else {
    output := IntToString((countA % 2) + (countA / 2));
  }
  steps := steps + 3;
}
