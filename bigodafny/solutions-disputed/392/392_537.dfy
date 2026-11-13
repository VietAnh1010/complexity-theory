// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : both
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny's `HasCommonChar` calls `CharInString(t, s[0])` for every
//     character of s, O(m**2) per pair and O(n*m**2) overall; the Python's
//     dict `map` makes each pair O(m), O(n*m) overall, so the label fits
//     neither program.
//
//   how this label could be wrong, and what to check:
//     The Python builds a dict over the first string and scans the second
//     once, O(n*m) for n pairs of length-m strings, so `O(n**2)` squares
//     the wrong size. The Dafny's `HasCommonChar` is a nested scan,
//     O(|s|*|t|) per pair. Check with disjoint strings, where no early
//     exit fires.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     1, "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1223_B. Strings Equalization  (problem 392, solution 392_537)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// for i in range(0, n):
//     first_string = input()
//     second_string = input()
// 
//     map = {}
// 
//     for i in range(0, len(first_string)):
//         if first_string[i] in map:
//             map[first_string[i]]+=1
//         else:
//             map[first_string[i]] = 1
//     
//     same = False
// 
//     for i in range(0, len(second_string)):
//         if second_string[i] in map:
//             same = True
//             break
//     
//     if same == True:
//         print("YES")
//     else:
//         print("NO")
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
