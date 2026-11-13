// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     For each test the Dafny computes `ISqrt(n)` and trial-divides up to
//     it, O(sqrt(n_i)) for a prime, so the cost is O(T * sqrt(max n_i));
//     the Python's loop to `math.ceil(math.sqrt(n))` pays the same.
//
//   how this label could be wrong, and what to check:
//     The label's n counts test cases, but each test trial-divides up to
//     ceil(sqrt(n_i)), a value term. Check the Dafny's `while i <= limit`
//     loop with `limit := ISqrt(n)`: a prime n_i runs it to the end, as
//     the Python's `range(2, ceil(sqrt(n))+1)` does.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 31, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1372_B. Omkar and Last Class of Math  (problem 1234, solution 1234_71)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// 
// def solve(n):
//     p = 1
//     for i in range(2, int(math.ceil(math.sqrt(n)))+1):
//         if n % i == 0:
//             p = i
//             break
//     if p != 1:
//         k = n//p
//     else:
//         k = 1
//     return " ".join([str(k), str(n - k)])
// 
// 
// def read():
//     t = int(input())
//     for i in range(t):
//         n = int(input())
//         ans = solve(n)
//         print(ans)
// 
// read()
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

ghost function SqrtSum(nums: seq<int>, n: int): nat
  requires n <= |nums|
  decreases n
{
  if n <= 0 then 0 else SqrtSum(nums, n - 1) + ISqrt(nums[n - 1]) + ISqrtSteps(nums[n - 1])
}

method Solve(N: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires N <= |numbers|
  ensures steps <= 40 * (if N > 0 then N else 0) + 14 + 8 * SqrtSum(numbers, N) + 3 * |output|
{
  var lines: seq<string> := [];
  steps := 6;
  var t := 0;
  while t < N
    invariant 0 <= t
    invariant t <= N || t == 0
    invariant |lines| == t
    invariant steps <= 6 + 30 * t + 8 * SqrtSum(numbers, t) + 2 * SumLen(lines)
    decreases N - t
  {
    var n := numbers[t];
    var p := 1;
    var limit := ISqrt(n);
    if limit * limit < n { limit := limit + 1; }
    steps := steps + 30 + ISqrtSteps(n);
    var i := 2;
    var found := false;
    ghost var s0 := steps;
    while i <= limit && !found
      invariant 2 <= i
      invariant i - 2 <= ISqrt(n)
      invariant steps == s0 + 8 * (i - 2)
      decreases limit - i
    {
      if n % i == 0 {
        p := i;
        found := true;
      }
      i := i + 1;
      steps := steps + 8;
    }
    var k := if p != 1 then FloorDiv(n, p) else 1;
    ghost var line := IntToString(k) + " " + IntToString(n - k);
    IntToStringDigits(k);
    IntToStringDigits(n - k);
    steps := steps + 2 * |line|;
    SumLenSnoc(lines, line);
    lines := lines + [IntToString(k) + " " + IntToString(n - k)];
    t := t + 1;
  }
  steps := steps + SumLen(lines) + |lines|;
  output := Join(lines, "\n");
  if |lines| >= 1 { JoinLen(lines, "\n"); }
}
