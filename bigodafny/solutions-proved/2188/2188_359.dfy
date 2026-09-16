// 1365_C. Rotation Matching  (problem 2188, solution 2188_359)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int,input().split()))
// b = list(map(int,input().split()))
// dif = [0]*n
// a = list(enumerate(a))
// b = list(enumerate(b))
// a.sort(key = lambda x:x[1])
// b.sort(key = lambda x:x[1])
// for i in range(n):
//     q1 = a[i][0]
//     q2 = b[i][0]
//     if q2-q1<0:
//         dif[i]=(n+(q2-q1))
//     else:
//         dif[i]=(q2-q1)
// maxi = 0
// difmax = [0]*n
// for s in dif:
//     difmax[s]+=1
//     if difmax[s]>maxi:
//         maxi = difmax[s]
// print(maxi)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Two Sort calls (each over n pairs), charged via the SortCost/CeilLog2
// recursion-tree technique used elsewhere for merge sort; the three
// following loops are all linear in n, charged 1 per element operation.

ghost function {:opaque} SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

lemma SquareSplit(k: nat, L: nat)
  requires 2 * L <= k <= 2 * L + 1
  ensures 2 * L * L + 2 * (k - L) * (k - L) <= k * k + 1
{
  var d := k - 2 * L;
  assert d == 0 || d == 1;
  assert k - L == L + d;
  assert 2 * L * L + 2 * (k - L) * (k - L) == 4 * L * L + 4 * L * d + 2 * d * d;
  assert k * k == 4 * L * L + 4 * L * d + d * d;
  assert d * d <= 1;
}

ghost function {:opaque} CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  reveal CeilLog2();
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
  reveal SortCost();
  reveal CeilLog2();
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

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |a_list| == n
  requires |b_list| == n
  ensures steps <= 4 * n * (CeilLog2(n) + 1) + 10 * n + 8
{
  steps := 1;
  var aPairs: seq<(int,int)> := [];
  var bPairs: seq<(int,int)> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |aPairs| == i
    invariant |bPairs| == i
    invariant forall k :: 0 <= k < i ==> aPairs[k].0 == k
    invariant forall k :: 0 <= k < i ==> bPairs[k].0 == k
    invariant steps == 2 * i + 1
    decreases n - i
  {
    aPairs := aPairs + [(i, a_list[i])];
    bPairs := bPairs + [(i, b_list[i])];
    i := i + 1;
    steps := steps + 2;
  }
  SortCostNLogN(n);
  var aSorted := Sort(aPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  var bSorted := Sort(bPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  steps := steps + 2 * SortCost(n);
  SortKeepsElems(aPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  SortKeepsElems(bPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  assert forall p :: p in aPairs ==> 0 <= p.0 < n;
  assert forall p :: p in bPairs ==> 0 <= p.0 < n;
  var dif: seq<int> := [];
  i := 0;
  ghost var base2 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant |dif| == i
    invariant forall k :: 0 <= k < i ==> 0 <= dif[k] < n
    invariant steps == base2 + 3 * i
    decreases n - i
  {
    assert aSorted[i] in aSorted;
    assert bSorted[i] in bSorted;
    var q1 := aSorted[i].0;
    var q2 := bSorted[i].0;
    var d := if q2 - q1 < 0 then n + (q2 - q1) else q2 - q1;
    dif := dif + [d];
    i := i + 1;
    steps := steps + 3;
  }
  var difmax := seq(if n >= 0 then n else 0, _ => 0);
  var maxi := 0;
  i := 0;
  ghost var base3 := steps;
  while i < |dif|
    invariant 0 <= i <= |dif|
    invariant |difmax| == n
    invariant forall k :: 0 <= k < |dif| ==> 0 <= dif[k] < n
    invariant steps == base3 + 3 * i
    decreases |dif| - i
  {
    var s := dif[i];
    difmax := difmax[s := difmax[s] + 1];
    if difmax[s] > maxi { maxi := difmax[s]; }
    i := i + 1;
    steps := steps + 3;
  }
  output := IntToString(maxi);
  steps := steps + 1;
}
