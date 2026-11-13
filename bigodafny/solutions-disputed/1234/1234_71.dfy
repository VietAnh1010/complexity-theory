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

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string)
  requires N <= |numbers|
{
  var lines: seq<string> := [];
  var t := 0;
  while t < N
    decreases N - t
  {
    var n := numbers[t];
    var p := 1;
    var limit := ISqrt(n);
    if limit * limit < n { limit := limit + 1; }
    var i := 2;
    var found := false;
    while i <= limit && !found
      decreases limit - i
    {
      if n % i == 0 {
        p := i;
        found := true;
      }
      i := i + 1;
    }
    var k := if p != 1 then FloorDiv(n, p) else 1;
    lines := lines + [IntToString(k) + " " + IntToString(n - k)];
    t := t + 1;
  }
  output := Join(lines, "\n");
}
