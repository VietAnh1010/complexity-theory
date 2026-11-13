// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's outer loop runs the literal 26 times and its inner loop
//     scans all of `text`, O(26 n) = O(n); the Python's `s.count(i)` for
//     each of 26 letters is the same 26 passes.
//
//   how this label could be wrong, and what to check:
//     The label is constant, but for each of 26 letters the Python calls
//     `s.count(i)`, a full scan of the text. Check that the text length
//     varies with the input; 26 scans of n characters is O(n), not O(1).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 29, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p02417 Counting Characters  (problem 3005, solution 3005_13)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// s=sys.stdin.read().lower()
// a=[print(i,':',s.count(i)) for i in map(chr,range(97,123))]
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string) returns (output: string, ghost steps: nat)
  ensures steps <= 260 * |text| + 2 * |output| + 240
{
  steps := 1;
  var lines: seq<string> := [];
  var letter := 0;
  while letter < 26
    invariant 0 <= letter <= 26
    invariant |lines| == letter
    invariant steps <= 1 + letter * (10 * |text| + 8) + SumLen(lines)
    decreases 26 - letter
  {
    ghost var base := steps;
    var c: char := (97 + letter) as char;
    var count := 0;
    var i := 0;
    while i < |text|
      invariant 0 <= i <= |text|
      invariant steps == base + 10 * i
      decreases |text| - i
    {
      var ch := text[i];
      var lc: char := if ch >= 'A' && ch <= 'Z' then ((ch as int) + 32) as char else ch;
      if lc == c {
        count := count + 1;
      }
      i := i + 1;
      steps := steps + 10;
    }
    var line := [c] + " : " + IntToString(count);
    IntToStringDigits(count);
    SumLenSnoc(lines, line);
    steps := steps + 8 + Digits(count);
    lines := lines + [line];
    CostMulDistrib(letter, 1, letter + 1, 10 * |text| + 8);
    letter := letter + 1;
  }
  output := Join(lines, "\n");
  JoinLen(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
  CostMulMonoLeft(26, 26, 10 * |text| + 8);
}
