// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-11
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     n (the cube count) is capped at 1<=n<=3 by the description, the
//     search while loop is bounded by the literal 1000, and
//     ContainsInt1722_66 scans each lists[k] of fixed 6-face length, so no
//     dimension here grows with input size and the true cost is O(1), not
//     O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes a growing n, but the description caps the cube
//     count at 1<=n<=3 and the search loop runs while i<1000, a fixed
//     bound. Check the description's constraint line for n; if it truly
//     tops out at 3, ContainsInt1722_66 scans only fixed-length face lists
//     and the whole method, in both languages, is O(1).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 67, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 887_B. Cubes for Masha  (problem 1722, solution 1722_66)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = []
// a += [list(input())]
// if (n > 1):
//     a += [list(input())]
// if (n > 2):
//     a += [list(input())]
// i = 1
// while (i < 1000):
//     s = list(str(i))
//     if (n == 1):
//         if (s[0] in a[0]):
//             i += 1
//             continue
//     if (n == 2):
//         if (len(s) == 1 and (s[0] in a[0] or s[0] in a[1])):
//             i += 1
//             continue
//         if (len(s) == 2 and (
//             (s[0] in a[0] and s[1] in a[1]) or
//             (s[0] in a[1] and s[1] in a[0]))):
//             i += 1
//             continue
//     if (n == 3):
//         if (len(s) == 1 and (s[0] in a[0] or s[0] in a[1] or s[0] in a[2])):
//             i += 1
//             continue
//         if (len(s) == 2 and (
//             (s[0] in a[0] and s[1] in a[1]) or
//             (s[0] in a[0] and s[1] in a[2]) or
//             (s[0] in a[1] and s[1] in a[0]) or
//             (s[0] in a[1] and s[1] in a[2]) or
//             (s[0] in a[2] and s[1] in a[0]) or
//             (s[0] in a[2] and s[1] in a[1]))):
//             i += 1
//             continue
//         if (len(s) == 3 and (
//             (s[0] in a[0] and s[1] in a[1] and s[2] in a[2]) or
//             (s[0] in a[0] and s[1] in a[2] and s[2] in a[1]) or
//             (s[0] in a[1] and s[1] in a[0] and s[2] in a[2]) or
//             (s[0] in a[1] and s[1] in a[2] and s[2] in a[0]) or
//             (s[0] in a[2] and s[1] in a[0] and s[2] in a[1]) or
//             (s[0] in a[2] and s[1] in a[1] and s[2] in a[0])
//             )):
//             i += 1
//             continue
//     print (i-1)
//     break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
  requires n <= |lists|
{
  var i := 1;
  var ans := 0;
  var done := false;
  while i < 1000 && !done
    decreases if done then 0 else 1000 - i
  {
    var s := Digits1722_66(i);
    var skip := false;
    if n == 1 {
      if ContainsInt1722_66(lists[0], s[0]) { skip := true; }
    } else if n == 2 {
      if |s| == 1 {
        if ContainsInt1722_66(lists[0], s[0]) || ContainsInt1722_66(lists[1], s[0]) { skip := true; }
      } else if |s| == 2 {
        if (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[1], s[1])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[0], s[1])) {
          skip := true;
        }
      }
    } else if n == 3 {
      if |s| == 1 {
        if ContainsInt1722_66(lists[0], s[0]) || ContainsInt1722_66(lists[1], s[0]) || ContainsInt1722_66(lists[2], s[0]) { skip := true; }
      } else if |s| == 2 {
        if (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[1], s[1])) ||
           (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[2], s[1])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[0], s[1])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[2], s[1])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[0], s[1])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[1], s[1])) {
          skip := true;
        }
      } else if |s| == 3 {
        if (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[1], s[1]) && ContainsInt1722_66(lists[2], s[2])) ||
           (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[2], s[1]) && ContainsInt1722_66(lists[1], s[2])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[0], s[1]) && ContainsInt1722_66(lists[2], s[2])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[2], s[1]) && ContainsInt1722_66(lists[0], s[2])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[0], s[1]) && ContainsInt1722_66(lists[1], s[2])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[1], s[1]) && ContainsInt1722_66(lists[0], s[2])) {
          skip := true;
        }
      }
    }
    if skip {
      i := i + 1;
    } else {
      ans := i - 1;
      done := true;
    }
  }
  output := IntToString(ans);
}

function Digits1722_66(i: int): seq<int>
  ensures 1 <= |Digits1722_66(i)| <= 3
{
  if i < 10 then [i]
  else if i < 100 then [i / 10, i % 10]
  else [i / 100, (i / 10) % 10, i % 10]
}

function ContainsInt1722_66(xs: seq<int>, v: int): bool
{
  exists k :: 0 <= k < |xs| && xs[k] == v
}
