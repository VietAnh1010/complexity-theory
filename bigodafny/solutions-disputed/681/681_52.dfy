// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     FactorialMod681 is called twice, each running a while loop `i <= n`
//     for n or m iterations, so the Dafny scales linearly with the scalar
//     inputs rather than being constant. Python's math.factorial(n) and
//     math.factorial(m) compute a genuinely growing product, which the
//     cost table's own rule flags as not O(1) for factorial-like
//     operations, so the O(1) label undercounts both sides.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 30, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
  requires mod != 0
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
