// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer loop calls `Valid(a_list, i, x, y)` for each i, `Valid`
//     loops i times, and its condition calls `SumSeq(l)` (linear) once s
//     is in [x, y], so the worst case is O(n**3); the Python's `sum(l)`
//     sits in the same place.
//
//   how this label could be wrong, and what to check:
//     The label counts the two nested loops but not `sum(l)` inside the
//     condition, an O(n) pass evaluated whenever the prefix sum lies in
//     [x, y]. With l = [1, 0, ..., 0, big] and x = y = 1, every prefix
//     reaches it and fails later, so `Valid(l, i)` costs O(i*n) and the
//     total is O(n**3). Check the condition's short-circuit order.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 47, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "SumSeq"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 357_A. Group of Students  (problem 894, solution 894_85)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// dumb = input()
// l = [int(o) for o in input().split()]
// x, y = [int(o) for o in input().split()]
// 
// def Valid(l, k, x, y):
//     s = 0
//     for i in range(k):
//         s += l[i]
//         if s >= x and s <= y and sum(l) - s >= x and sum(l) - s <= y and s != sum(l) and s != 0 and sum(l) - s != 0:
//             return True
//     return False
// 
// for i in range(len(l)):
//     if Valid(l, i, x, y):
//         break
// if i+1 > 0 and i < len(l) and Valid(l, i, x, y):
//     print(i+1)
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Valid(l: seq<int>, k: int, x: int, y: int) returns (r: bool)
  requires 0 <= k <= |l|
{
  var s := 0;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    decreases k - i
  {
    s := s + l[i];
    if s >= x && s <= y && SumSeq(l) - s >= x && SumSeq(l) - s <= y && s != SumSeq(l) && s != 0 && SumSeq(l) - s != 0 {
      return true;
    }
    i := i + 1;
  }
  return false;
}

method Solve(n: int, a_list: seq<int>, x: int, y: int) returns (output: string)
{
  var i := 0;
  var broke := false;
  while i < |a_list| && !broke
    invariant 0 <= i <= |a_list|
    decreases |a_list| - i, if broke then 0 else 1
  {
    var v := Valid(a_list, i, x, y);
    if v {
      broke := true;
    } else {
      i := i + 1;
    }
  }
  if !broke {
    i := |a_list| - 1;
  }
  var ok := false;
  if i + 1 > 0 && i < |a_list| {
    ok := Valid(a_list, i, x, y);
  }
  if ok {
    output := IntToString(i + 1) + "\n";
  } else {
    output := "0\n";
  }
}
