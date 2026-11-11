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
  ensures r >= 0 && r * r <= v && v < (r + 1) * (r + 1)
  ensures steps <= 7 * v + 10
{
  steps := 0;
  var lo := 0;
  steps := steps + 1;
  var hi := v + 1;
  assert (v + 1) * (v + 1) == v * v + 2 * v + 1;
  assert v * v >= 0;
  while lo < hi
    invariant 0 <= lo <= hi <= v + 1
    invariant hi >= 1
    invariant lo == 0 || (lo - 1) * (lo - 1) <= v
    invariant hi * hi > v
    invariant steps <= 1 + 7 * (v + 1 - (hi - lo))
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
      if mid == 0 { assert mid * mid == 0; }
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

lemma SqMono(a: int, b: int)
  requires 0 <= b <= a
  ensures b * b <= a * a
{
  assert b * b <= a * b;
  assert a * b <= a * a;
}

lemma RepLen(s: string, m: int)
  requires |s| == 1
  ensures |RepStr(s, m)| == (if m > 0 then m else 0)
  decreases if m > 0 then m else 0
{
  if m > 0 { RepLen(s, m - 1); }
}

lemma RepStepsBound(s: string, m: int)
  requires |s| == 1
  ensures RepStr_steps(s, m) <= 2 + 3 * (if m > 0 then m else 0) + (if m > 0 then m else 0) * (if m > 0 then m else 0)
  decreases if m > 0 then m else 0
{
  if m > 0 {
    RepStepsBound(s, m - 1);
    RepLen(s, m - 1);
    assert (m - 1) * (m - 1) == m * m - 2 * m + 1;
  }
}

lemma RepBound(m: int, nn: int)
  requires m <= nn && nn >= 0
  ensures RepStr_steps("a", m) <= 2 + 3 * nn + nn * nn
  ensures |RepStr("a", m)| <= nn
{
  RepStepsBound("a", m);
  RepLen("a", m);
  var p := if m > 0 then m else 0;
  SqMono(nn, p);
}

lemma RowFacts(nn: int, k: int, val: int, s: int, x: int, d: int, b: int, y: int)
  requires nn >= 3 && k >= 1 && 2 * k <= nn * (nn - 1)
  requires val == 8 * k - 7 && s >= 0 && s * s <= val && val < (s + 1) * (s + 1)
  requires x == FloorDiv(1 + s, 2) && d == FloorDiv(s - 1, 2)
  requires b == FloorDiv(d * (d + 1), 2) + 1 && y == k - b
  ensures 0 <= x <= nn && 0 <= y <= nn
  ensures val + 4 * nn + 7 <= 4 * (nn * nn)
{
  assert nn * (nn - 1) == nn * nn - nn;
  assert (2 * nn) * (2 * nn) == 4 * (nn * nn);
  if s == 0 { assert (s + 1) * (s + 1) == 1; }
  if s >= 2 * nn { SqMono(s, 2 * nn); }
  assert s < 2 * nn;
  assert x == (1 + s) / 2;
  assert d == (s - 1) / 2;
  var dd := d * d;
  assert dd >= 0;
  assert d * (d + 1) == dd + d;
  var h := (dd + d) / 2;
  assert b == h + 1;
  if s == 2 * d + 1 {
    assert s * s == 4 * dd + 4 * d + 1;
    assert (s + 1) * (s + 1) == 4 * dd + 8 * d + 4;
  } else {
    assert s == 2 * d + 2;
    assert s * s == 4 * dd + 8 * d + 4;
    assert (s + 1) * (s + 1) == 4 * dd + 12 * d + 9;
  }
}

ghost function RowB(row: seq<int>): nat
{
  if |row| >= 2 && row[0] >= 0 then 7 + 31 * (row[0] * row[0]) else 7
}

ghost function Tot(ps: seq<seq<int>>, t: nat): nat
  requires t <= |ps|
  decreases t
{
  if t == 0 then 0 else Tot(ps, t - 1) + RowB(ps[t - 1])
}

lemma TotStep(ps: seq<seq<int>>, t: nat)
  requires t < |ps|
  ensures Tot(ps, t + 1) == Tot(ps, t) + RowB(ps[t])
{
}

method Solve(n: int, pairs_list: seq<seq<int>>)
    returns (output: string, ghost steps: nat)
  requires forall t :: 0 <= t < |pairs_list| && |pairs_list[t]| >= 2 ==> pairs_list[t][0] >= 3 && 1 <= pairs_list[t][1] && 2 * pairs_list[t][1] <= pairs_list[t][0] * (pairs_list[t][0] - 1)
  ensures steps <= Tot(pairs_list, |pairs_list|) + |output| + 3
{
  steps := 0;
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
    invariant steps <= Tot(pairs_list, t)
  {
    ghost var start := steps;
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
      assert nn == pairs_list[t][0] && k == pairs_list[t][1];
      RowFacts(nn, k, val, s, x, d, b, y);
      RepBound(nn - x - 1, nn);
      RepBound(x - y - 1, nn);
      RepBound(y, nn);
      assert nn * nn == row[0] * row[0];
      steps := steps + (4 + RepStr_steps("a", nn - x - 1) + |"b"| + RepStr_steps("a", x - y - 1) + |RepStr("a", x - y - 1)| + |"b"| + RepStr_steps("a", y) + |RepStr("a", y)|);
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      steps := steps + (1 + |[r]|);
      results := results + [r];
    }
    steps := steps + 1;
    TotStep(pairs_list, t);
    t := t + 1;
  }
  steps := steps + 2;
  steps := steps + (SumLen(results) + |results|);
  output := Join(results, "\n");
  if |results| >= 1 { JoinLen(results, "\n"); }
}

import opened Prelude
