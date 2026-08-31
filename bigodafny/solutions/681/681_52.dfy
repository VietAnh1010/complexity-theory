// p03683 AtCoder Regular Contest 076 - Reconciled?  (problem 681, solution 681_52)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// mod=10**9+7
// import math
// if m==n:
//     print((math.factorial(n)*math.factorial(m)*2)%mod)
// elif abs(n-m)==1:
//     print((math.factorial(n)*math.factorial(m))%mod)
// else:
//     print(0)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var mod := 1000000007;
  var diff := if a >= b then a - b else b - a;
  if a == b {
    var fa := FactorialMod681(a, mod);
    var fb := FactorialMod681(b, mod);
    output := IntToString((fa * fb % mod) * 2 % mod);
  } else if diff == 1 {
    var fa := FactorialMod681(a, mod);
    var fb := FactorialMod681(b, mod);
    output := IntToString((fa * fb) % mod);
  } else {
    output := IntToString(0);
  }
}

method FactorialMod681(n: int, mod: int) returns (r: int)
{
  r := 1;
  var i := 1;
  while i <= n
    decreases n - i + 1
  {
    r := (r * i) % mod;
    i := i + 1;
  }
}
