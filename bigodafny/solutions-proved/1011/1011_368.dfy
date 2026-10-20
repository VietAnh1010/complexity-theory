// 1099_B. Squares and Segments  (problem 1011, solution 1011_368)
// time complexity: O(sqrt(n))
// label corrected 2026-10-20: BigOBench says O(n); this proof bounds steps by 12 * CSqrt(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # http://codeforces.com/contest/1099/problem/B
// n = int(input())
// a = b = 1
// while a * b < n:
//     if a < b:
//         a += 1
//     else:
//         b += 1
// 
// print(a+b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function CSqrt(n: int): nat
  decreases if n < 0 then 0 else n
{
  if n <= 1 then 1 else
    var r := 2 * CSqrt((n + 3) / 4);
    if (r - 1) * (r - 1) >= n then r - 1 else r
}

lemma Sq(a: int, b: int)
  requires 1 <= a <= b <= a + 1
  ensures (a + b) * (a + b) <= 4 * (a * b) + 1
{
  if b == a { assert (a + b) * (a + b) == 4 * (a * a); }
  else { assert (a + b) * (a + b) == 4 * (a * b) + 1; }
}

lemma SqLt(x: int, y: int)
  requires 0 <= x && 0 <= y && x * x < y * y
  ensures x < y
{
  if x >= y { Mul(y, x); }
}

lemma Mul(x: int, y: int)
  requires 0 <= x <= y
  ensures x * x <= y * y
{
}

lemma CSqrtSq(n: int)
  ensures CSqrt(n) >= 1 && CSqrt(n) * CSqrt(n) >= n
  decreases if n < 0 then 0 else n
{
  if n > 1 {
    var m := (n + 3) / 4;
    CSqrtSq(m);
    var q := CSqrt(m);
    assert q >= 1;
    assert q * q >= m;
    assert 4 * m >= n;
    assert (2 * q) * (2 * q) == 4 * (q * q);
    var r := 2 * q;
    assert r * r >= n;
    if (r - 1) * (r - 1) >= n {
      assert r >= 2;
    }
  }
}

lemma DigitsLe(x: int)
  requires x >= 1
  ensures Digits(x) <= x
  decreases x
{
  if x >= 10 { DigitsLe(x / 10); }
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * CSqrt(n)
{
  steps := 0;
  var a := 1;
  var b := 1;
  CSqrtSq(n);
  ghost var R := CSqrt(n);
  while a * b < n
    invariant 1 <= a <= b <= a + 1
    invariant steps == 5 * (a + b - 2)
    invariant a + b <= 2 * R
    decreases n - a * b
  {
    CSqrtSq(n);
    Sq(a, b);
    Mul(0, 0);
    assert (a + b) * (a + b) < 4 * (R * R);
    SqLt(a + b, 2 * R);
    steps := steps + 3;
    steps := steps + 1;
    if a < b {
      steps := steps + 1;
      a := a + 1;
    } else {
      steps := steps + 1;
      b := b + 1;
    }
  }
  DigitsLe(a + b);
  steps := steps + 2;
  steps := steps + (1 + Digits(a + b));
  output := IntToString(a + b);
}

