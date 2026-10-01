// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(1)
//   cause          : harness
//   confidence     : medium
//   auditor        : labelaudit-r3-15
//
//   Both artifacts are right. The Python pays to parse stdin and
//   BigOBench profiled the whole script; the Dafny's Solve receives the
//   inputs already parsed, so that cost is outside the measured method.
//   Nothing to repair -- document it.
//
//   evidence:
//     The `while |a| > 0 && |b| > 0 && k <= 1000` loop is bounded by the
//     literal 1000 and does O(1) work per iteration (`a[1..] + [b0, a0]`
//     appends two elements), and Solve never scans list1 or list2 beyond
//     index 0, so the Dafny is O(1). The Python's O(n+m) comes from
//     parsing both lines and slicing `a[1:]`, which is outside Solve's
//     boundary.
//
//   how this label could be wrong, and what to check:
//     The label O(n+m) assumes Solve scans both card lists. Open the Dafny
//     and check that the only list accesses are a[0] and b[0] inside a
//     loop capped by the literal `k <= 1000`; if so Solve is O(1) and the
//     O(n+m) comes from the Python's input parsing (`a = a[1:]`, list
//     comprehensions), i.e. the harness boundary.
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
