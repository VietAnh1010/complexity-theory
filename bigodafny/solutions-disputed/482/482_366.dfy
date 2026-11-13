// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n+m)log(n+m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop runs bv from 0 to max(a, b) and calls `ISqrt(n - bv)` each
//     time, charged its O(log) recursion depth, so the cost is O((n+m)
//     log(n+m)); the Python calls `math.sqrt` at the same point in every
//     iteration.
//
//   how this label could be wrong, and what to check:
//     The label counts the loop to max(n, m) but charges each square root
//     1. Check the loop body: `ISqrt(n - bv)` runs on every iteration and
//     costs O(log n). The Python takes `math.sqrt(n-b)` on every iteration
//     too, so the label, not the translation, omits the term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 22, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 214_A. System of Equations  (problem 482, solution 482_366)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// k=list(map(int,input().split()))
// n=max(k)
// m=min(k)
// p=0
// for b in range(0,n+1):
//     if b<=n:
//         a=math.sqrt(n-b)
//         if m>=a:
//             if b==math.sqrt(m-a):
//                 if int(b)==b and int(a)==a:
//                     p+=1
// print(p)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var n := if a > b then a else b;
  var m := if a < b then a else b;
  var count := 0;
  var bv := 0;
  while bv <= n
    decreases n - bv
  {
    var av := ISqrt(n - bv);
    if av * av == n - bv && m >= av {
      var sv := ISqrt(m - av);
      if sv * sv == m - av && bv == sv {
        count := count + 1;
      }
    }
    bv := bv + 1;
  }
  output := IntToString(count);
}
