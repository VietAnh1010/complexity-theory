include "../../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * (if a > 0 then a else 0) + 6 * (if b > 0 then b else 0) + 20 + |output|
{
  var mod := 1000000007;
  var diff := if a >= b then a - b else b - a;
  steps := 6;
  if a == b {
    var fa, s1 := FactorialMod681(a, mod);
    var fb, s2 := FactorialMod681(b, mod);
    output := IntToString((fa * fb % mod) * 2 % mod);
    IntToStringDigits((fa * fb % mod) * 2 % mod);
    steps := steps + s1 + s2 + 6 + Digits((fa * fb % mod) * 2 % mod);
  } else if diff == 1 {
    var fa, s1 := FactorialMod681(a, mod);
    var fb, s2 := FactorialMod681(b, mod);
    output := IntToString((fa * fb) % mod);
    IntToStringDigits((fa * fb) % mod);
    steps := steps + s1 + s2 + 4 + Digits((fa * fb) % mod);
  } else {
    output := IntToString(0);
    IntToStringDigits(0);
    steps := steps + 2 + Digits(0);
  }
}

method FactorialMod681(n: int, mod: int) returns (r: int, ghost steps: nat)
  requires mod != 0
  ensures steps <= 6 * (if n > 0 then n else 0) + 2
{
  r := 1;
  var i := 1;
  steps := 2;
  while i <= n
    invariant i >= 1
    invariant i <= (if n > 0 then n else 0) + 1
    invariant steps <= 6 * (i - 1) + 2
    decreases n - i + 1
  {
    r := (r * i) % mod;
    i := i + 1;
    steps := steps + 6;
  }
}
