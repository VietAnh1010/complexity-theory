// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-12
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Python defines unused helper functions `getdict` and `prime`
//     containing loops, but the executed program is only `h, m = map(int,
//     input().split(':'))` followed by `print((h % 12) * 30 + m / 2, m *
//     6)`, so its real complexity is O(1), same as the Dafny's
//     straight-line ParseInt/arithmetic body.
//
//   how this label could be wrong, and what to check:
//     The label may have been derived from the `prime(n)` function's `for
//     d in range(3, sqr, 2)` loop or `getdict`'s loops defined earlier in
//     the Python file. Check whether `prime` or `getdict` is ever called
//     after their definitions; in this file only `h, m = map(int,
//     input().split(':'))` and the final `print(...)` execute, so the true
//     runtime is O(1), matching the Dafny's loop-free body.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 12, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt"],
//     "loop_depth": 0, "loops": 0, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 80_B. Depression  (problem 1855, solution 1855_50)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// import math
// import itertools
// import collections
// 
// def getdict(n):
//     d = {}
//     if type(n) is list or type(n) is str:
//         for i in n:
//             if i in d:
//                 d[i] += 1
//             else:
//                 d[i] = 1
//     else:
//         for i in range(n):
//             t = ii()
//             if t in d:
//                 d[t] += 1
//             else:
//                 d[t] = 1
//     return d
// def cdiv(n, k): return n // k + (n % k != 0)
// def ii(): return int(input())
// def mi(): return map(int, input().split())
// def li(): return list(map(int, input().split()))
// def lcm(a, b): return abs(a*b) // math.gcd(a, b)
// def wr(arr): return ' '.join(map(str, arr))
// def revn(n): return int(str(n)[::-1])
// def prime(n):
//     if n == 2: return True
//     if n % 2 == 0 or n <= 1: return False
//     sqr = int(math.sqrt(n)) + 1
//     for d in range(3, sqr, 2):
//         if n % d == 0: return False
//     return True
// 
// h, m = map(int, input().split(':'))
// print((h % 12) * 30 + m / 2, m * 6)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(hour: string, minute: string) returns (output: string)
{
  var h := ParseInt(hour);
  var m := ParseInt(minute);
  var num := 60 * (h % 12) + m;
  var half := num / 2;
  var firstStr := if num % 2 == 0 then IntToString(half) + ".0" else IntToString(half) + ".5";
  var second := m * 6;
  output := firstStr + " " + IntToString(second);
}
