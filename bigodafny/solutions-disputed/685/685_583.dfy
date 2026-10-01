// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn+mlogm)
//   audited class  : O(n+m)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-02
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python sorts both arrays with sorted() and reads the last
//     element, which is O(n log n + m log m), while the Dafny calls Max685
//     on each list, a single linear scan, giving O(n+m). The translation
//     replaced the sort by a maximum scan, so the label fits the Python
//     and not the Dafny.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's two `sorted(...)` calls followed
//     by `[-1]`. Check that Max685 is a single linear scan with no Sort
//     call and that the Python really sorts both int_array_a and
//     int_array_b.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 21, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1206_A. Choose Two Numbers  (problem 685, solution 685_583)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num_n = int(input())
// input_a = input()
// array_a = input_a.split(" ")
// num_m = int(input())
// input_b = input()
// array_b = input_b.split(" ")
// int_array_a = []
// for i in array_a:
// 	int_array_a.append(int(i))
// int_array_b = []
// for i in array_b:
// 	int_array_b.append(int(i))
// int_array_a = sorted(int_array_a)
// int_array_b = sorted(int_array_b)
// print(int_array_a[-1], int_array_b[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n1: int, list1: seq<int>, n2: int, list2: seq<int>) returns (output: string)
  requires |list1| > 0 && |list2| > 0
{
  var max1 := Max685(list1);
  var max2 := Max685(list2);
  output := IntToString(max1) + " " + IntToString(max2);
}

method Max685(xs: seq<int>) returns (m: int)
  requires |xs| > 0
{
  m := xs[0];
  var i := 1;
  while i < |xs|
    decreases |xs| - i
  {
    if xs[i] > m { m := xs[i]; }
    i := i + 1;
  }
}
