// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-s03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The nested while loops run i from 1 to a and j from 1 to b, the two
//     input values M and D, with O(1) work inside, so the cost is a
//     product of two different values, O(n*m), not one size squared. The
//     Python's range(1,M+1) over range(1,D+1) pays the same product.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) names one size squared, but the loops are bounded
//     by two different inputs, M (months) and D (days per month). Check
//     the signature Solve(a, b) and the two loop guards `i <= a` and `j <=
//     b`; the statement caps (M at most 100, D at most 99) are not source
//     literals, so they do not make either bound constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p02927 Japanese Student Championship 2019 Qualification - Takahashi Calendar  (problem 1954, solution 1954_83)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// M,D=map(int,input().split())
// cnt=0
// for i in range(1,M+1):
//     for j in range(1,D+1):
//         iti=j%10
//         ju=j//10
//         if iti>=2 and ju>=2 and i==iti*ju:
//             cnt+=1
// 
// print(cnt)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var cnt := 0;
  var i := 1;
  while i <= a
    decreases a - i + 1
  {
    var j := 1;
    while j <= b
      decreases b - j + 1
    {
      var iti := j % 10;
      var ju := j / 10;
      if iti >= 2 && ju >= 2 && i == iti * ju {
        cnt := cnt + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  output := IntToString(cnt);
}
