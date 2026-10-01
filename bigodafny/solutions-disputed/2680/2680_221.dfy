// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(1)
//   cause          : translation
//   confidence     : low
//   auditor        : labelaudit-r4-d03
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The loop `while |a| > 0 && |b| > 0 && k <= 1000` has a literal 1000
//     cap and each round does O(1) work (a[1..] is a view, concat appends
//     two elements), so the Dafny is O(1) in the list sizes. The Python's
//     pop(0) shifts the remaining list each round, so its rounds cost
//     O(|a|+|b|), matching the label; I lean translation (the slicing
//     shape), but the Python's n+m dependence is small.
//
//   how this label could be wrong, and what to check:
//     The label matches a Python that does `a.pop(0)`, `b.pop(0)` and list
//     appends on lists of the card counts, which shift elements and cost
//     O(n+m) per round. Check that the Dafny uses `a[1..] + [b0, a0]`, a
//     view plus a two-element concat, inside a loop whose bound k <= 1000
//     is a source literal.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 29, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 546_C. Soldier and Cards  (problem 2680, solution 2680_221)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// a = a[1:]
// b = [int(x) for x in input().split()]
// b = b[1:]
// k = 0
// while len(a) > 0 and len(b) > 0 and k <= 10 ** 3:
// 	if a[0] > b[0] and (not(a[0] == 0 and b[0] == 9) and not(a[0] == 9 and b[0] == 0)):
// 		a.append(b[0])
// 		a.append(a[0])
// 		a.pop(0)
// 		b.pop(0)
// 		k += 1
// 	else:
// 		b.append(a[0])
// 		b.append(b[0])
// 		a.pop(0)
// 		b.pop(0)
// 		k += 1
// if len(a) != 0 and len(b) != 0:
// 	print(-1)
// elif len(a) > 0:
// 	print(k, 1)
// else:
// 	print(k, 2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, list1: seq<int>, list2: seq<int>) returns (output: string)
{
  var a := list1;
  var b := list2;
  var k := 0;
  while |a| > 0 && |b| > 0 && k <= 1000
    decreases 1001 - k
  {
    var a0 := a[0];
    var b0 := b[0];
    if a0 > b0 && !(a0 == 0 && b0 == 9) && !(a0 == 9 && b0 == 0) {
      a := a[1..] + [b0, a0];
      b := b[1..];
    } else {
      b := b[1..] + [a0, b0];
      a := a[1..];
    }
    k := k + 1;
  }
  if |a| != 0 && |b| != 0 {
    output := "-1";
  } else if |a| > 0 {
    output := JoinInts([k, 1], " ");
  } else {
    output := JoinInts([k, 2], " ");
  }
}
