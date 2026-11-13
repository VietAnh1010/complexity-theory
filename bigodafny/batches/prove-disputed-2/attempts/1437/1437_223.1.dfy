// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python sorts `valores` and then scans for 1, O(n log n) as
//     labelled; the Dafny's whole body is `1 in a_list`, a linear
//     membership test, O(n), so the sort was dropped.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's `valores.sort()` before its
//     membership scan. Check that the Dafny never sorts and just tests `1
//     in a_list`, a linear scan; without the sort it is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 6, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 560_A. Currency System in Geraldion  (problem 1437, solution 1437_223)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def meuIn(num, valores):
//     for i in valores:
//         if(i == num):
//             return True
//         if(i > num):
//             return False
//     return False
// 
// def verificaValores(valores):
// 
//     if(not meuIn(1, valores)):
//         return 1
// 
//     return -1
// 
// num = int(input())
// entrada = input().split()
// 
// valores = [int(valor) for valor in entrada]
// valores.sort()
// 
// print(verificaValores(valores))
// 	 	 		  	  			 	  	 	 		 	  	 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= |a_list| + 2 * |output| + 3
{
  var r := if 1 in a_list then -1 else 1;
  steps := |a_list| + 1;
  output := IntToString(r);
  IntToStringDigits(r);
  steps := steps + Digits(r);
}
