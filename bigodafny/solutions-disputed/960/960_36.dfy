// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops over each of the n strings once, inserting into a
//     set of at most 26 letters and sorting that set, so the cost is
//     O(n*m) for n strings of length m, as in the Python.
//
//   how this label could be wrong, and what to check:
//     The code is n test strings each scanned once, plus a sort of at most
//     26 distinct letters per string. By the naming rule that is O(n*m),
//     not one size squared. Check that the sort input `g` is a set of
//     lowercase letters, so it is constant-size.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 47, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     3, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     true, "sorts": ["Sort"], "uses_map": false, "uses_multiset": false,
//     "uses_set": true}
// --------------------------------------------------------------------

// 1251_A. Broken Keyboard  (problem 960, solution 960_36)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
//     s = list(input().strip())
//     g = set()
//     n = len(s)
//     c = 1
//     if n==1:
//         print(s[0])
//     else:
//         for i in range(1,n):
//             if s[i]!=s[i-1] and c&1:
//                 g.add(s[i-1])
//             else:
//                 c += 1
//             if i==n-1 and c&1:
//                 g.add(s[i])
//         print(''.join(sorted(list(g))))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var lines: seq<string> := [];
  var si := 0;
  while si < |strings|
    decreases |strings| - si
  {
    var s := strings[si];
    var m := |s|;
    var lineOut: string;
    if m == 1 {
      lineOut := [s[0]];
    } else {
      var g: set<char> := {};
      var c := 1;
      var i := 1;
      while i < m
        decreases m - i
      {
        if s[i] != s[i-1] && c % 2 == 1 {
          g := g + {s[i-1]};
        } else {
          c := c + 1;
        }
        if i == m-1 && c % 2 == 1 {
          g := g + {s[i]};
        }
        i := i + 1;
      }
      var elems: seq<char> := [];
      var gg := g;
      while gg != {}
        decreases |gg|
      {
        var x :| x in gg;
        elems := elems + [x];
        gg := gg - {x};
      }
      lineOut := Sort(elems, (a, b) => a < b);
    }
    lines := lines + [lineOut];
    si := si + 1;
  }
  output := Join(lines, "\n");
}
