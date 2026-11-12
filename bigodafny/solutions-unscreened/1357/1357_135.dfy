// 1331_B. Limericks  (problem 1357, solution 1357_135)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// n = int(sys.stdin.readline().strip())
// L = []
// i = 2
// while n > 1:
//     if n % i == 0:
//         L.append(str(i))
//         n = n // i
//     else:
//         i = i + 1
// print("".join(L))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulGe(d: int, x: int)
  requires d > 0 && x >= 1
  ensures d * x >= d
{}
lemma MultipleMod(a: int, d: int)
  requires d > 0
  ensures (d * a) % d == 0
{
  var q := (d * a) / d;
  var r := (d * a) % d;
  assert d * a == d * q + r;
  assert d * (a - q) == r;
  if a - q >= 1 { MulGe(d, a - q); }
  else if a - q <= -1 { MulGe(d, q - a); assert d * (q - a) == -r; }
}
lemma DivisorOfQuotient(m: int, i: int, d: int)
  requires i >= 2 && d >= 2 && m % i == 0 && m > 0
  requires (m / i) % d == 0
  ensures m % d == 0
{
  var q := m / i;
  var k := q / d;
  assert q == d * k;
  assert m == i * q;
  assert m == d * (k * i);
  MultipleMod(k * i, d);
}

method Solve(n: int) returns (output: string)
{
{

  var m := n;
  var i := 2;
  var parts: seq<string> := [];
  while m > 1
    invariant 2 <= i
    invariant forall d :: 2 <= d < i ==> m % d != 0
    invariant m > 1 ==> i <= m
    decreases m, m - i
  {
    if m % i == 0 {
      forall d | 2 <= d < i
        ensures (m / i) % d != 0
      {
        if (m / i) % d == 0 { DivisorOfQuotient(m, i, d); }
      }
      if 1 < m / i < i {
        assert m == (m / i) * i;
        MultipleMod(i, m / i);
      }
      parts := parts + [IntToString(i)];
      m := m / i;
    } else {
      i := i + 1;
    }
  }
  output := Join(parts, "");
}
}
