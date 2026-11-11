// --- Python ---------------------------------------------------------
// # Anuneet Anand
// import math
// T = int(input())
//
// while T:
// 	n,k = map(int,input().split())
// 	x = int(((1) + math.sqrt(1 + (8 * (k-1)))) / 2)
// 	d = int(math.floor((-1 + math.sqrt(1+ 8 * k - 8)) / 2))
// 	b = (d * (d + 1)) / 2 + 1
// 	y = int(k - b)
// 	A = ['a' for i in range(n)]
// 	A[n-x-1]='b'
// 	A[n-y-1]='b'
// 	R = "a"*(n-x-1)+"b"+"a"*(x-y-1)+"b" + y*"a"
// 	print(R)
// 	T = T-1
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method IntSqrtFloor(v: int) returns (r: int, ghost steps: nat)
  requires v >= 0
  ensures r * r <= v < (r + 1) * (r + 1)
  ensures steps <= 7 * (CeilLog2(v + 1) + 1) + 3
{
  steps := 0;
  var lo := 0;
  steps := steps + 1;
  var hi := v + 1;
  ghost var it: nat := 0;
  assert (v + 1) * (v + 1) == v * v + 2 * v + 1;
  assert v * v >= 0 by { CostMulMono(v, 0, v); }
  while lo < hi
    invariant 0 <= lo <= hi
    invariant lo == 0 || (lo - 1) * (lo - 1) <= v
    invariant v < hi * hi
    invariant steps <= 1 + 7 * it
    invariant it + SearchPot(hi - lo) <= SearchPot(v + 1)
    decreases hi - lo
  {
    ghost var k := hi - lo;
    steps := steps + 2;
    steps := steps + 2;
    var mid := (lo + hi) / 2;
    steps := steps + 2;
    if mid * mid <= v {
      steps := steps + 1;
      lo := mid + 1;
    } else {
      hi := mid;
    }
    BisectStep(k, hi - lo);
    it := it + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  r := lo - 1;
  if hi == 0 {
    assert hi * hi == 0;
  }
  assert SearchPot(0) == 0;
  assert it <= SearchPot(v + 1);
}

function RepStr(s: string, n: int): string
  decreases if n > 0 then n else 0
{
  if n <= 0 then
    ""
  else
    s + RepStr(s, n - 1)
}

ghost function RepStr_steps(s: string, n: int): nat
  decreases if n > 0 then n else 0
{
  2 + if n <= 0 then 0 else 1 + RepStr_steps(s, n - 1) + |RepStr(s, n - 1)|
}

ghost function Pow2(j: nat): nat
{
  if j == 0 then 1 else 2 * Pow2(j - 1)
}

lemma LogPow(m: nat, j: nat)
  requires m <= Pow2(j)
  ensures CeilLog2(m) <= j
  decreases j
{
  if j > 0 && m > 1 {
    LogPow((m + 1) / 2, j - 1);
  }
}

lemma Pow2Sq(j: nat)
  ensures (j + 1) * (j + 1) <= Pow2(2 * j)
  decreases j
{
  if j > 0 {
    Pow2Sq(j - 1);
    assert Pow2(2 * j) == 4 * Pow2(2 * (j - 1));
    assert j * j >= j by { CostMulMono(j, 1, j); }
    assert (j + 1) * (j + 1) == j * j + 2 * j + 1;
    assert (j - 1 + 1) * (j - 1 + 1) == j * j;
  }
}

lemma LogLin(nn: nat, k: nat)
  requires 3 <= nn && 1 <= k && 2 * k <= nn * nn - nn
  ensures CeilLog2(8 * k - 7 + 1) <= 4 * nn
{
  Pow2Sq(2 * nn);
  assert (2 * nn + 1) * (2 * nn + 1) == 4 * (nn * nn) + 4 * nn + 1;
  LogPow(8 * k - 7 + 1, 2 * (2 * nn));
}

lemma QBound(m: int)
  requires m >= 0
  ensures |RepStr("a", m)| == m
  ensures RepStr_steps("a", m) <= m * m + 2 * m + 2
  decreases m
{
  if m > 0 {
    QBound(m - 1);
    assert (m - 1) * (m - 1) == m * m - 2 * m + 1;
  }
}

lemma SqMono(a: nat, b: nat)
  requires a <= b
  ensures a * a <= b * b
{
  CostMulMono(a, a, b);
  CostMulMonoLeft(a, b, b);
}

lemma SumSq(a: nat, b: nat, c: nat)
  ensures a * a + b * b + c * c <= (a + b + c) * (a + b + c)
{
  CostMulMono(a, 0, b);
  CostMulMono(b, 0, c);
  CostMulMono(a, 0, c);
  assert (a + b + c) * (a + b + c) == a * a + b * b + c * c + 2 * (a * b) + 2 * (b * c) + 2 * (a * c);
}

lemma Sq2(a: nat, b: nat)
  ensures a * a + b * b <= (a + b) * (a + b)
{
  CostMulMono(a, 0, b);
  assert (a + b) * (a + b) == a * a + b * b + 2 * (a * b);
}

lemma RowFacts(nn: int, k: int, s: int, x: int, d: int, b: int, y: int)
  requires 3 <= nn && 1 <= k && 2 * k <= nn * nn - nn
  requires 0 <= s && s * s <= 8 * k - 7 < (s + 1) * (s + 1)
  requires x == FloorDiv(1 + s, 2) && d == FloorDiv(s - 1, 2) && b == FloorDiv(d * (d + 1), 2) + 1 && y == k - b
  ensures 0 <= nn - x - 1 && 0 <= x - y - 1 && 0 <= y
{
  if s == 0 { assert s * s == 0; }
  assert s >= 1;
  assert x == (1 + s) / 2;
  assert d == (s - 1) / 2;
  assert d >= 0;
  assert x == d + 1;
  assert d * (d + 1) >= 0 by { CostMulMono(d, 0, d + 1); }
  var w := d * (d + 1);
  assert w == d * d + d;
  var e := w / 2;
  assert b == e + 1;
  // w is even
  var q := d / 2;
  if d % 2 == 0 {
    assert d == 2 * q;
    assert w == 2 * (q * (d + 1));
  } else {
    assert d == 2 * q + 1;
    assert w == 2 * (d * (q + 1));
  }
  assert w == 2 * e;
  var D := d * d;
  assert 2 * d + 1 <= s;
  assert s <= 2 * d + 2;
  SqMono(2 * d + 1, s);
  SqMono(s + 1, 2 * d + 3);
  assert (2 * d + 1) * (2 * d + 1) == 4 * D + 4 * d + 1;
  assert (2 * d + 3) * (2 * d + 3) == 4 * D + 12 * d + 9;
  assert k >= e + 1;
  assert k <= e + d + 1;
  if d >= nn - 1 {
    SqMono(nn - 1, d);
    CostMulMono(d, nn - 1, d + 1);
    CostMulMonoLeft(nn - 1, d, nn);
    assert (nn - 1) * nn == nn * nn - nn;
    assert d * (d + 1) >= (nn - 1) * nn;
    assert false;
  }
}

method Solve(n: int, pairs_list: seq<seq<int>>)
    returns (output: string, ghost steps: nat)
  requires forall t :: 0 <= t < |pairs_list| && |pairs_list[t]| >= 2 ==> pairs_list[t][0] >= 3 && 1 <= pairs_list[t][1] && 2 * pairs_list[t][1] <= pairs_list[t][0] * (pairs_list[t][0] - 1)
  ensures steps <= 21 * (|output| * |output|) + 9 * |pairs_list| + 2
{
  steps := 0;
  var results: seq<string> := [];
  ghost var sq: nat := 0;
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
    invariant steps <= 20 * sq + 8 * t
    invariant sq <= SumLen(results) * SumLen(results)
    invariant |results| <= t
  {
    ghost var st0 := steps;
    ghost var res0 := results;
    steps := steps + 3;
    steps := steps + 1;
    var row := pairs_list[t];
    steps := steps + 2;
    if |row| >= 2 {
      steps := steps + 1;
      var nn := row[0];
      steps := steps + 1;
      var k := row[1];
      steps := steps + 2;
      var val := 8 * k - 7;
      steps := steps + 1;
      if val < 0 {
        val := 0;
      }
      var s, s0 := IntSqrtFloor(val);
      steps := steps + s0;
      steps := steps + (1 + 1);
      var x := FloorDiv(1 + s, 2);
      steps := steps + (1 + 1);
      var d := FloorDiv(s - 1, 2);
      steps := steps + (3 + 1);
      var b := FloorDiv(d * (d + 1), 2) + 1;
      steps := steps + 1;
      var y := k - b;
      steps := steps + (4 + RepStr_steps("a", nn - x - 1) + |"b"| + RepStr_steps("a", x - y - 1) + |RepStr("a", x - y - 1)| + |"b"| + RepStr_steps("a", y) + |RepStr("a", y)|);
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      steps := steps + (1 + |[r]|);
      results := results + [r];
      assert row == pairs_list[t];
      assert nn >= 3 && 1 <= k && 2 * k <= nn * (nn - 1);
      assert nn * (nn - 1) == nn * nn - nn;
      assert val == 8 * k - 7;
      LogLin(nn, k);
      RowFacts(nn, k, s, x, d, b, y);
      QBound(nn - x - 1);
      QBound(x - y - 1);
      QBound(y);
      SumSq(nn - x - 1, x - y - 1, y);
      assert nn - x - 1 + (x - y - 1) + y == nn - 2;
      assert (nn - 2) * (nn - 2) == nn * nn - 4 * nn + 4;
      assert |r| == nn;
      SumLenSnoc(res0, r);
      Sq2(SumLen(res0), nn);
      CostMulMonoLeft(3, nn, nn);
      assert steps <= st0 + 19 * (nn * nn);
      sq := sq + nn * nn;
    }
    steps := steps + 1;
    t := t + 1;
  }
  steps := steps + 2;
  steps := steps + (SumLen(results) + |results|);
  output := Join(results, "\n");
  if |results| >= 1 {
    JoinLen(results, "\n");
  }
  assert SumLen(results) <= |output|;
  SqMono(SumLen(results), |output|);
  if |output| >= 1 {
    CostMulMono(|output|, 1, |output|);
  }
  assert SumLen(results) <= |output| * |output|;
}

import opened Prelude
