// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     For each of the T values the Dafny trial-divides `while i * i <= n`,
//     up to sqrt(n_i) steps for a prime, and the Python's `factors(n)`
//     generator always runs that far, so both are O(T * sqrt(max n_i)), a
//     value term the label omits.
//
//   how this label could be wrong, and what to check:
//     The label counts test cases, but each test runs trial division up to
//     sqrt(n_i), a cost in the VALUE of n_i: the Python's `factors` loops
//     `while i * i <= n` in full. Check the Dafny's inner `while i * i <=
//     n` loop; a prime n_i makes both run sqrt(n_i) steps, so the class is
//     O(T sqrt(max n_i)).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 29, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1372_B. Omkar and Last Class of Math  (problem 1234, solution 1234_634)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def factors(n):
//     i = 1
//     while i * i <= n:
//         if n % i == 0:
//             yield i
//             yield n // i
//         i += 1
// 
// for t in range(int(input())):
//     n = int(input())
//     s = sorted(list(factors(n)))[-2]
//     print(s, n - s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function SumISqrt(s: seq<int>, n: nat): nat
  requires n <= |s|
  decreases n
{
  if n == 0 then 0 else SumISqrt(s, n - 1) + ISqrt(s[n - 1])
}

method Solve(N: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires N <= |numbers|
  ensures steps <= 10 * SumISqrt(numbers, if N < 0 then 0 else N) + 21 * (if N < 0 then 0 else N) + 3 * |output| + 10
{
  steps := 1;
  var lines: seq<string> := [];
  var t := 0;
  while t < N
    invariant 0 <= t
    invariant t <= N || N < 0 || t == 0
    invariant |lines| == t
    invariant steps <= 1 + 20 * t + 10 * SumISqrt(numbers, t) + 2 * SumLen(lines)
    decreases N - t
  {
    var n := numbers[t];
    var p := 1;
    var found := false;
    var i := 2;
    ghost var base := steps;
    steps := steps + 20;
    while i * i <= n && !found
      invariant 2 <= i <= ISqrt(n) + 2
      invariant steps <= base + 20 + 10 * (i - 2)
      decreases n - i
    {
      LeISqrt(i, n);
      if n % i == 0 {
        p := i;
        found := true;
      }
      i := i + 1;
      steps := steps + 10;
    }
    var s := if found then FloorDiv(n, p) else 1;
    var line := IntToString(s) + " " + IntToString(n - s);
    IntToStringDigits(s);
    IntToStringDigits(n - s);
    SumLenSnoc(lines, line);
    steps := steps + 2 * |line|;
    lines := lines + [line];
    t := t + 1;
  }
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
  if |lines| >= 1 { JoinLen(lines, "\n"); }
}
