// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(logn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's `while m > 1` loop increments `i` by one until it
//     divides m, so it runs up to the largest prime factor of n, O(n) in
//     the value n; the Python's trial-division loop is identical.
//
//   how this label could be wrong, and what to check:
//     The label counts the number of prime factors, but `i` steps up by
//     one until it reaches the largest prime factor. The input is a
//     product of two primes, so the loop runs to the larger one, about n/2
//     steps for n = 2 * p. Check the `else: i = i + 1` branch; it makes
//     the cost linear in the value n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 60, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 3,
//     "seq_append_read_in_same_loop": false, "seq_args": 0,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
