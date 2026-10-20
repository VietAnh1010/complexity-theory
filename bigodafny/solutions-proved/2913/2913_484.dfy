// 1088_A. Ehab and another construction problem  (problem 2913, solution 2913_484)
// time complexity: O(sqrt(n))
// label corrected 2026-10-20: BigOBench says O(n); this proof bounds steps by 10 * Isqrt(n) + 30
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def Calculo_Brute_Force(x):
//
//     for a in range(1,x+1):
//             if ((a*a)>x) :
//                 print (a,a)
//                 return(a,a)
//
//     print(-1)
//     return(-1)
//
// Calculo_Brute_Force(int(input()))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 10 * Isqrt(n) + 30
{
  steps := 0;
  var a := 1;
  var found := false;
  var ans := 0;
  while a <= n && !found
    invariant 1 <= a
    invariant !found ==> steps <= 7 * (a - 1) && (a - 1) * (a - 1) <= (if n > 0 then n else 0)
    invariant found ==> steps <= 7 * (a - 1) + 6 && a == ans && (a - 1) * (a - 1) <= n && a * a > n && 1 <= a
    decreases n - a, if found then 0 else 1
  {
    steps := steps + (3 + if a <= n then 1 else 0);
    steps := steps + 2;
    if a * a > n {
      ans := a;
      found := true;
    } else {
      steps := steps + 1;
      a := a + 1;
    }
  }
  steps := steps + (2 + if a <= n then 1 else 0);
  IsqrtSpec(n);
  SqrtLe(a - 1, Isqrt(n), if n > 0 then n else 0);
  assert a - 1 <= Isqrt(n);
  if found {
    DigitsLe(ans);
    IntToStringDigits(ans);
    assert Digits(ans) <= Isqrt(n) + 1;
    steps := steps + (Digits(ans) + |" "| + Digits(ans) + |IntToString(ans)| + |"\n"|);
    output := IntToString(ans) + " " + IntToString(ans) + "\n";
  } else {
    output := "-1\n";
  }
}


ghost function Isqrt(n: int): nat
{
  if n < 4 then (if n >= 1 then 1 else 0) else 2 * Isqrt(n / 4) + (if (2*Isqrt(n/4)+1)*(2*Isqrt(n/4)+1) <= n then 1 else 0)
}

lemma IsqrtSpec(n: int)
  ensures n >= 0 ==> Isqrt(n) * Isqrt(n) <= n < (Isqrt(n) + 1) * (Isqrt(n) + 1)
  ensures n < 1 ==> Isqrt(n) == 0
  decreases if n < 0 then 0 else n
{
  if n >= 4 {
    IsqrtSpec(n / 4);
    var r := Isqrt(n / 4);
    assert n / 4 * 4 <= n < n / 4 * 4 + 4;
    assert r * r <= n / 4 < (r + 1) * (r + 1);
    assert 4 * (r * r) <= n;
    assert n < 4 * ((r + 1) * (r + 1));
    if (2 * r + 1) * (2 * r + 1) <= n {
      assert (2 * r + 2) * (2 * r + 2) == 4 * ((r + 1) * (r + 1));
    } else {
      assert (2 * r) * (2 * r) <= n;
    }
  }
}

lemma SqrtLe(m: int, r: int, n: int)
  requires 0 <= m && m * m <= n && n >= 0
  requires r >= 0 && (n < (r + 1) * (r + 1) || n == 0)
  ensures m <= r
{
  if m > r { assert m >= r + 1; assert m * m >= (r + 1) * (r + 1); if n == 0 { assert m * m >= 1; } }
}

lemma DigitsLe(x: int)
  requires x >= 1
  ensures Digits(x) <= x
  decreases x
{
  if x >= 10 { DigitsLe(x / 10); }
}
