// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny's `HasCommonChar` recurses over s and calls
//     `CharInString(t, ...)` per character, O(|s|*|t|) per pair, so
//     O(n*m**2) overall; the Python intersects two sets in O(|s|+|t|),
//     O(n*m), so neither matches O(n).
//
//   how this label could be wrong, and what to check:
//     Two faults. The Python is O(n*m) (set(s) & set(t) per pair, n pairs
//     of length-m strings), so O(n) misses the string length. The Dafny's
//     `HasCommonChar` calls `CharInString(t, s[0])` for each character of
//     s, O(|s|*|t|) per pair. Check with s all 'a' and t all 'b': no early
//     exit, m**2 steps per pair.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     1, "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1223_B. Strings Equalization  (problem 392, solution 392_411)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin, stdout
// from math import gcd
// input = stdin.readline
// 
// for _ in range(int(input())):
//     s = input()[:-1]
//     t = input()[:-1]
//     if set(s) & set(t):
//         print('YES')
//     else:
//         print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CharInString(s: string, c: char): bool
  decreases |s|
{
  if |s| == 0 then false
  else if s[0] == c then true
  else CharInString(s[1..], c)
}

function HasCommonChar(s: string, t: string): bool
  decreases |s|
{
  if |s| == 0 then false
  else if CharInString(t, s[0]) then true
  else HasCommonChar(s[1..], t)
}

method Solve(n: int, string_pairs: seq<(string, string)>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |string_pairs|
    decreases |string_pairs| - i
  {
    if HasCommonChar(string_pairs[i].0, string_pairs[i].1) {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n");
}
