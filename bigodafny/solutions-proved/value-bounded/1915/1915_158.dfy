// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
// 1155_C. Alarm Clocks Everywhere  (problem 1915, solution 1915_158)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
//
// n,m=[int(i) for i in input().split()]
// x=[int(i) for i in input().split()]
// p=[int(i) for i in input().split()]
// x_2=[]
// for i in range(1,len(x)):
//     x_2.append(x[i]-x[i-1])
// g=x_2[0]
// for i in range(1,len(x_2)):
//     g=math.gcd(g,x_2[i])
// b=False
// for i in range (0,len(p)):
//     if(g%p[i]==0):
//         print('YES')
//         print(x[0],i+1)
//         b=True
//         break
// if(not(b)):
//     print('NO')
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

function GcdNN(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures GcdNN(a, b) >= 0
  ensures GcdNN(a, b) == Gcd(a, b)
  decreases b
{
  if b == 0 then a else GcdNN(b, a % b)
}

// The most bits of any gap |s[k] - s[k-1]|, 1 <= k < i: what the gcd loop reads.
ghost function MaxGapBits(s: seq<int>, i: nat): nat
  requires 2 <= i <= |s|
  decreases i
{
  var bits := BitLen(AbsInt(s[i - 1] - s[i - 2]));
  if i == 2 then bits
  else var before := MaxGapBits(s, i - 1); if before >= bits then before else bits
}

// Euclid's depth telescopes: two steps halve the second argument, and the
// result is at least the gcd, so the depth is twice the bits it loses.
lemma GcdTelescope(a: int, b: int)
  requires a >= 0 && b >= 1
  ensures Gcd(a, b) >= 1
  ensures GcdSteps(a, b) + 2 * CeilLog2(Gcd(a, b) + 1) <= 2 * CeilLog2(b + 1) + 3
  decreases b
{
  GcdLeSecond(a, b);
  var r1 := a % b;
  if r1 > 0 {
    var r2 := b % r1;
    assert GcdSteps(a, b) == 2 + GcdSteps(r1, r2);
    assert Gcd(a, b) == Gcd(r1, r2);
    if r2 == 0 {
      CeilLog2Monotone(r1 + 1, b + 1);
    } else {
      // r2 < b / 2: either r1 is at most half of b, or b % r1 == b - r1
      if 2 * r1 > b { ModUpper(b, r1); }
      assert 2 * r2 < b;
      GcdTelescope(r1, r2);
      assert r2 + 1 <= (b + 2) / 2;
      CeilLog2Monotone(r2 + 1, (b + 2) / 2);
      assert CeilLog2(b + 1) == 1 + CeilLog2((b + 2) / 2);
    }
  }
}

// The same, measured on the first argument: one more step brings it second.
lemma GcdTelescopeFirst(a: int, b: int)
  requires a >= 1 && b >= 0
  ensures Gcd(a, b) >= 1
  ensures GcdSteps(a, b) + 2 * CeilLog2(Gcd(a, b) + 1) <= 2 * CeilLog2(a + 1) + 4
{
  GcdLeFirst(a, b);
  if b > 0 {
    var r := a % b;
    assert GcdSteps(a, b) == 1 + GcdSteps(b, r);
    assert Gcd(a, b) == Gcd(b, r);
    if r == 0 {
      CeilLog2Monotone(b + 1, a + 1);
    } else {
      GcdTelescope(b, r);
      if a < b { SmallMod(a, b); }
      CeilLog2Monotone(r + 1, a + 1);
    }
  }
}

lemma GcdZero(x: int)
  requires x >= 0
  ensures GcdSteps(0, x) <= 2 && Gcd(0, x) == x
{
  if x > 0 {
    assert 0 % x == 0;
    assert GcdSteps(0, x) == 1 + GcdSteps(x, 0);
    assert Gcd(0, x) == Gcd(x, 0);
  }
}

// Each GcdNN call costs Euclid's recursion depth, GcdSteps (GcdNN recurses
// as Gcd does). The running gcd g only shrinks once it is positive, so the
// depths telescope (GcdTelescopeFirst): the loop costs O(n) plus 4 times the
// bits of the largest gap. g is 0 only while every gap so far is 0.
method Solve(n: int, m: int, n_list: seq<int>, m_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 2
  requires m >= 0
  requires |n_list| >= n
  requires |m_list| >= m
  requires forall t :: 0 <= t < |m_list| ==> m_list[t] >= 1
  ensures steps <= 6 * n + 3 * m + 4 * MaxGapBits(n_list, n) + 6 + |output|
{
  steps := 1;
  var g := AbsInt(n_list[1] - n_list[0]);
  var i := 2;
  steps := steps + 2;
  while i < n
    invariant 2 <= i <= n
    invariant g >= 0
    invariant g == 0 ==> MaxGapBits(n_list, i) == 0
    invariant steps + 2 * CeilLog2(g + 1) <= 6 * (i - 2) + 3 + 4 * MaxGapBits(n_list, i)
    decreases n - i
  {
    ghost var x := AbsInt(n_list[i] - n_list[i - 1]);
    assert MaxGapBits(n_list, i + 1) >= MaxGapBits(n_list, i);
    assert MaxGapBits(n_list, i + 1) >= CeilLog2(x + 1);
    if g == 0 { GcdZero(x); } else { GcdTelescopeFirst(g, x); }
    steps := steps + 2 + GcdSteps(g, AbsInt(n_list[i] - n_list[i - 1]));
    g := GcdNN(g, AbsInt(n_list[i] - n_list[i - 1]));
    i := i + 1;
  }
  var found := false;
  var idx := 0;
  var j := 0;
  steps := steps + 1;
  while j < m && !found
    invariant 0 <= j <= m
    invariant steps <= 6 * n + 4 * MaxGapBits(n_list, n) + 2 * j - 8
    decreases m - j
  {
    if g % m_list[j] == 0 {
      found := true;
      idx := j;
    }
    j := j + 1;
    steps := steps + 2;
  }
  if found {
    output := "YES\n" + IntToString(n_list[0]) + " " + IntToString(idx + 1);
    IntToStringDigits(n_list[0]);
    IntToStringDigits(idx + 1);
    steps := steps + Digits(n_list[0]) + Digits(idx + 1);
  } else {
    output := "NO";
  }
  steps := steps + 1;
}
