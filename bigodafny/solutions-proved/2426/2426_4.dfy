// 839_B. Game of the Rows  (problem 2426, solution 2426_4)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// seat = {4:n, 2:n*2, 1:0}
// extra1 = 0
// a = sorted(map(int, input().split()), reverse=True)
//
// def sit(n, m):
//     num = min(seat[n], m)
//     seat[n] -= num
//     return m - num
//
// for m in a:
//     p4 = m // 4
//     p3, p2, p1 = 0, 0, 0
//     if m%4 == 3:
//         p3 = 1
//     else:
//         p2 = int(m % 4 > 1)
//         p1 = int(m % 2)
//
//     extra4 = sit(4, p4)
//     p2 += extra4*2
//     if sit(4, p3) > 0:
//         p2 += 1
//         p1 += 1
//
//     extra2 = sit(2, p2)
//     x = sit(4, extra2)
//     seat[1] += extra2 - x
//     p1 += x * 2
//
//     extra1 += p1
//
// extra1 = sit(1, extra1)
// x = sit(4, extra1)
// seat[2] += extra1 - x
// y = sit(2, x)
//
// if y > 0:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// One Sort call over `values` (the only superlinear term); the loop over the
// sorted values does a fixed, bounded amount of arithmetic per element
// (calls to the local Sit function, itself O(1)), so it is charged O(1) per
// iteration. Total: O(n log n) from the sort, plus O(n) from the loop.

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

function Sit(cap: int, req: int): (int, int)
{
  var num := if cap < req then cap else req;
  (cap - num, req - num)
}

method Solve(n: int, m: int, values: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |values| * (CeilLog2(|values|) + 1) + 20 * |values| + 10
{
  steps := 1;
  SortCostNLogN(|values|);
  var sortedVals := Sort(values, (x: int, y: int) => x > y);
  steps := steps + SortCost(|values|);
  var seat4 := n;
  var seat2 := n * 2;
  var seat1 := 0;
  var extra1sum := 0;
  var idx := 0;
  ghost var base1 := steps;
  while idx < |sortedVals|
    invariant 0 <= idx <= |sortedVals|
    invariant steps == base1 + 15 * idx
    decreases |sortedVals| - idx
  {
    var mm := sortedVals[idx];
    var p4 := FloorDiv(mm, 4);
    var p3 := 0;
    var p2 := 0;
    var p1 := 0;
    if FloorMod(mm, 4) == 3 {
      p3 := 1;
    } else {
      p2 := if FloorMod(mm, 4) > 1 then 1 else 0;
      p1 := FloorMod(mm, 2);
    }

    var r1 := Sit(seat4, p4);
    seat4 := r1.0;
    var extra4 := r1.1;
    p2 := p2 + extra4 * 2;

    var r2 := Sit(seat4, p3);
    seat4 := r2.0;
    var sitres3 := r2.1;
    if sitres3 > 0 {
      p2 := p2 + 1;
      p1 := p1 + 1;
    }

    var r3 := Sit(seat2, p2);
    seat2 := r3.0;
    var extra2 := r3.1;

    var r4res := Sit(seat4, extra2);
    seat4 := r4res.0;
    var x := r4res.1;
    seat1 := seat1 + (extra2 - x);
    p1 := p1 + x * 2;

    extra1sum := extra1sum + p1;
    idx := idx + 1;
    steps := steps + 15;
  }

  var f1 := Sit(seat1, extra1sum);
  seat1 := f1.0;
  var e1 := f1.1;
  var f2 := Sit(seat4, e1);
  seat4 := f2.0;
  var x2 := f2.1;
  seat2 := seat2 + (e1 - x2);
  var f3 := Sit(seat2, x2);
  seat2 := f3.0;
  var y := f3.1;
  steps := steps + 3;

  output := if y > 0 then "NO" else "YES";
}
