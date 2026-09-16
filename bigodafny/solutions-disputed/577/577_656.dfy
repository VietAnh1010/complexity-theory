// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r2-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Resolved by review with the problem statement: 1345_B gives up to t
//     <= 1000 test cases each with a value n <= 10^9. Pyramid is
//     O(sqrt(value)), so a single query costs at most about 31623 steps
//     regardless of how many queries there are. Total cost is linear in
//     the query count, not quadratic.
//
//   how this label could be wrong, and what to check:
//     The label reads as quadratic in the query count. Check the Input
//     section: the per-test value n is capped at 10^9 independently of t,
//     so the per-query sqrt work is a constant factor and the total is
//     O(t). If instead the label's n means a single query's magnitude, the
//     row is O(sqrt(n)) and still not quadratic. Sibling 577_509 carries
//     O(n) for the same signature convention.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 39, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1345_B. Card Constructions  (problem 577, solution 577_656)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from typing import List
// def pyramid():
//     n = int(input())
//     aux = n
//     respuesta = 1
//     altura = 1
//     if(n<2):
//         respuesta = 0
//     while(aux>=2):
//         aux = aux - 2*altura - altura + 1
//         if( aux < 0 ):
//             aux = aux + 2*altura + altura - 1
//             altura = 1
//             respuesta = respuesta + 1
//         else:
//             altura = altura + 1
//     print(respuesta)
// t = int(input())
// for i in range(t):
//     pyramid()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers_list: seq<int>) returns (output: string)
  requires forall t :: 0 <= t < |numbers_list| ==> numbers_list[t] >= 1
{

  var results: seq<string> := [];
  var i := 0;
  while i < |numbers_list|
    invariant 0 <= i <= |numbers_list|
    decreases |numbers_list| - i
  {
    var r := Pyramid(numbers_list[i]);
    results := results + [IntToString(r)];
    i := i + 1;
  }
  output := Join(results, "\n");
}


method Pyramid(nVal: int) returns (respuesta: int)
  requires nVal >= 0
{
  var aux := nVal;
  respuesta := 1;
  var altura := 1;
  if nVal < 2 { respuesta := 0; }
  while aux >= 2
    invariant aux >= 0
    invariant altura >= 1
    decreases aux, altura
  {
    aux := aux - 2 * altura - altura + 1;
    if aux < 0 {
      aux := aux + 2 * altura + altura - 1;
      altura := 1;
      respuesta := respuesta + 1;
    } else {
      altura := altura + 1;
    }
  }
}
