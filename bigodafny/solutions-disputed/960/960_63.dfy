// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny scans each of the n strings once with the run loop and
//     sorts a set of at most 26 letters per string, O(n*m); the Python's
//     `sorted(i)` likewise sorts a constant-size set.
//
//   how this label could be wrong, and what to check:
//     The label's log factor can only come from `sorted(i)`, which sorts
//     at most 26 letters, a constant. Check that each set holds only
//     lowercase letters; then the cost is one scan per string, O(n*m) for
//     n strings of length m.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 46, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 3, "loops":
//     4, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     true, "sorts": ["Sort"], "uses_map": false, "uses_multiset": false,
//     "uses_set": true}
// --------------------------------------------------------------------

// 1251_A. Broken Keyboard  (problem 960, solution 960_63)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// r = []
// for i in ' '*n:
//   s = input()
//   m = []
//   t = set()
//   j = 0
//   while j < len(s):
//     if s[j] not in t:
//       c = 1
//       while j < len(s)-1 and s[j] == s[j+1]:
//         j += 1
//         c += 1
//       if c % 2 == 1:
//         t.add(s[j])
//     j += 1
//   r += [t]
// for i in r:
//   print(*sorted(i), sep='')
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
    var mlen := |s|;
    var tset: set<char> := {};
    var j := 0;
    while j < mlen
      invariant 0 <= j <= mlen
      decreases mlen - j
    {
      if s[j] !in tset {
        var c := 1;
        while j < mlen - 1 && s[j] == s[j+1]
          invariant 0 <= j < mlen
          decreases mlen - j
        {
          j := j + 1;
          c := c + 1;
        }
        if c % 2 == 1 {
          tset := tset + {s[j]};
        }
      }
      j := j + 1;
    }
    var elems: seq<char> := [];
    var gg := tset;
    while gg != {}
      decreases |gg|
    {
      var x :| x in gg;
      elems := elems + [x];
      gg := gg - {x};
    }
    lines := lines + [Sort(elems, (a, b) => a < b)];
    si := si + 1;
  }
  output := Join(lines, "\n");
}
