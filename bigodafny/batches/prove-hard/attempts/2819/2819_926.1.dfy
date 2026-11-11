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
  ensures 0 <= r <= v
  ensures steps <= 7 * v + 10
{
  steps := 0;
  var lo := 0;
  steps := steps + 1;
  var hi := v + 1;
  while lo < hi
    invariant 0 <= lo <= hi <= v + 1
    invariant hi > 0
    invariant steps <= 1 + 7 * ((v + 1) - (hi - lo))
    decreases hi - lo
  {
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
  }
  steps := steps + 1;
  steps := steps + 1;
  r := lo - 1;
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

ghost function Sq(x: nat): nat { x * x }

ghost function Mb(nn: nat, k: nat): nat { nn + Sq(8 * k) + 16 * k + 1 }

ghost function RowB(row: seq<int>): nat
{
  if |row| >= 2 && row[0] >= 0 && row[1] >= 1 then
    3 * Sq(Mb(row[0] as nat, row[1] as nat) + 2) + 2 * Mb(row[0] as nat, row[1] as nat) + 56 * (row[1] as nat) + 45
  else 0
}

ghost function PB(pl: seq<seq<int>>, t: nat): nat
  requires t <= |pl|
  decreases t
{
  if t == 0 then 0 else PB(pl, t - 1) + RowB(pl[t - 1]) + 7
}

lemma SqMono(a: nat, b: nat)
  requires a <= b
  ensures Sq(a) <= Sq(b)
{
  CostMulMonoLeft(a, b, a);
  CostMulMono(b, a, b);
}

lemma RepExact(m: int)
  ensures |RepStr("a", m)| == (if m > 0 then m else 0)
  ensures RepStr_steps("a", m) <= Sq((if m > 0 then m else 0) + 2)
  decreases if m > 0 then m else 0
{
  if m > 0 {
    RepExact(m - 1);
    assert RepStr_steps("a", m) == 2 + 1 + RepStr_steps("a", m - 1) + |RepStr("a", m - 1)|;
    var mm: nat := m;
    var mp: nat := if m - 1 > 0 then m - 1 else 0;
    assert mp == m - 1;
    assert Sq(mp + 2) == (m + 1) * (m + 1);
    assert Sq(mm + 2) == (m + 2) * (m + 2);
  }
}

lemma RepBound(m: int, M: nat)
  requires m <= M
  ensures |RepStr("a", m)| <= M
  ensures RepStr_steps("a", m) <= Sq(M + 2)
{
  RepExact(m);
  var mm: nat := if m > 0 then m else 0;
  assert mm <= M;
  SqMono(mm + 2, M + 2);
}

lemma DBound(d: int, K: nat)
  requires -1 <= d <= K
  ensures 0 <= d * (d + 1) <= Sq(K) + K
{
  if d >= 0 {
    var dn: nat := d;
    CostMulMonoLeft(dn, K, dn + 1);
    CostMulMono(K, dn + 1, K + 1);
    assert K * (K + 1) == Sq(K) + K;
  }
}

method Solve(n: int, pairs_list: seq<seq<int>>)
    returns (output: string, ghost steps: nat)
  requires forall t :: 0 <= t < |pairs_list| && |pairs_list[t]| >= 2 ==> pairs_list[t][0] >= 3 && 1 <= pairs_list[t][1] && 2 * pairs_list[t][1] <= pairs_list[t][0] * (pairs_list[t][0] - 1)
  ensures steps <= PB(pairs_list, |pairs_list|) + |output| + 3
{
  steps := 0;
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
    invariant steps <= PB(pairs_list, t)
  {
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
      ghost var K: nat := (8 * k) as nat;
      assert val <= K;
      assert x == (1 + s) / 2;
      assert d == (s - 1) / 2;
      assert x <= K;
      assert -1 <= d <= K;
      DBound(d, K);
      assert b == (d * (d + 1)) / 2 + 1;
      ghost var M: nat := Mb(nn as nat, k as nat);
      assert M == nn + Sq(K) + 16 * k + 1;
      assert nn - x - 1 <= M;
      assert x - y - 1 <= M;
      assert y <= M;
      RepBound(nn - x - 1, M);
      RepBound(x - y - 1, M);
      RepBound(y, M);
      steps := steps + (4 + RepStr_steps("a", nn - x - 1) + |"b"| + RepStr_steps("a", x - y - 1) + |RepStr("a", x - y - 1)| + |"b"| + RepStr_steps("a", y) + |RepStr("a", y)|);
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      steps := steps + (1 + |[r]|);
      results := results + [r];
    }
    steps := steps + 1;
    t := t + 1;
    assert PB(pairs_list, t) == PB(pairs_list, t - 1) + RowB(pairs_list[t - 1]) + 7;
  }
  steps := steps + 2;
  steps := steps + (SumLen(results) + |results|);
  output := Join(results, "\n");
  if |results| >= 1 {
    JoinLen(results, "\n");
  } else {
    assert SumLen(results) == 0;
  }
}

import opened Prelude
