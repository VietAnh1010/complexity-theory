// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve calls ContainsChar, FindFirst and FindLast, each recursing
//     once per character of arrows (O(|arrows|) = O(n)); the Python's `'<'
//     not in s`, s.find and s.rfind are also linear scans of the string.
//
//   how this label could be wrong, and what to check:
//     The label assumes constant work, but the string of bumpers must be
//     scanned. Check ContainsChar, FindFirst and FindLast in Solve, each
//     recursing over arrows, and the Python's `in`, find and rfind on the
//     string, all linear.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 38, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 3, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 725_A. Jumping Ball  (problem 410, solution 410_176)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, s = int(input()), input()
// if '<' not in s or '>' not in s:
//     print(n)
// else:
//     print(s.find('>') + (n - 1 - s.rfind('<')))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, arrows: string) returns (output: string)
{
  var hasLt := ContainsChar(arrows, '<');
  var hasGt := ContainsChar(arrows, '>');
  if !hasLt || !hasGt {
    output := IntToString(n) + "\n";
  } else {
    var fi := FindFirst(arrows, '>');
    var la := FindLast(arrows, '<');
    output := IntToString(fi + (n - 1 - la)) + "\n";
  }
}

function ContainsChar(s: string, c: char): bool
  decreases |s|
{
  if |s| == 0 then false
  else if s[0] == c then true
  else ContainsChar(s[1..], c)
}

function FindFirst(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else 1 + FindFirst(s[1..], c)
}

function FindLast(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then -1
  else
    var rest := FindLast(s[1..], c);
    if rest >= 0 then 1 + rest
    else if s[0] == c then 0
    else -1
}
