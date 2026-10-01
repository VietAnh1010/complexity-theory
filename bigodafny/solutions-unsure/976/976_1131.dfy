// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n)
//   cause          : unclear
//   confidence     : low
//   auditor        : labelaudit-r4-s02
//
//   Which of the label or the translation is at fault was not determined
//   by the audit.
//
//   evidence:
//     The first loop runs once per element of a_list with O(1) map
//     updates, but each element goes through ParseInt, whose cost is the
//     token's length, so by the naming rule this is n strings each scanned
//     once; the later d.Keys iteration is O(|d|). The tokens are numerals
//     of at most 3 digits.
//
//   how this label could be wrong, and what to check:
//     The label O(n) assumes ParseInt(a_list[i]) is constant per element.
//     Check whether numeral width counts as a size m (ParseIntFrom
//     recurses once per character): if so the label should be O(n*m). If
//     numeral digit count is treated as constant, as the proof of 378_91
//     seems to, O(n) stands. Also confirm that `keys - {k}` in the Keys
//     loop is not charged O(|keys|), which would make that loop quadratic.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 41, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt",
//     "ParseIntFrom"], "loop_depth": 1, "loops": 2, "recursive_helpers":
//     2, "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": true, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1003_A. Polycarp's Pockets  (problem 976, solution 976_1131)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = list(map(int, input().split()))
// 
// d = dict()
// for a in arr:
//     if not a in d:
//         d[a] = 0
//     d[a] += 1
// 
// maxn = 0
// for a in d:
//     maxn = max(maxn, d[a])
// 
// print(maxn)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}


method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var d: map<int, int> := map[];
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var a := ParseInt(a_list[i]);
    if a in d {
      d := d[a := d[a] + 1];
    } else {
      d := d[a := 1];
    }
    i := i + 1;
  }
  var maxn := 0;
  var keys := d.Keys;
  while keys != {}
    invariant keys <= d.Keys
    decreases |keys|
  {
    var k :| k in keys;
    if d[k] > maxn { maxn := d[k]; }
    keys := keys - {k};
  }
  output := IntToString(maxn);
}
