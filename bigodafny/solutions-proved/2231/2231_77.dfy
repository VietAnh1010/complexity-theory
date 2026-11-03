// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n)
//   cause          : unclear
//   confidence     : low
//   auditor        : labelaudit-r4-u01
//
//   Which of the label or the translation is at fault was not determined
//   by the audit.
//
//   evidence:
//     The outer loop runs n+1 times and on every letter change the inner
//     loop copies `entries`, whose size is the number of distinct letters,
//     so cost is O(n*d); with the statement's 26-letter alphabet d is a
//     constant and the row is O(n) like the Python, but no requires in the
//     Dafny enforces that bound.
//
//   how this label could be wrong, and what to check:
//     The label O(n) holds only if the number of distinct letters is a
//     constant. Open Solve and find the inner `while j < |entries|` loop
//     that rebuilds newEntries each time the letter changes: its length is
//     the distinct-letter count d, so cost is O(n*d) where the Python's
//     dict is O(1) per change. Check whether you count the statement's
//     lowercase alphabet (d <= 26) as constant; if not the Dafny is
//     O(n**2) worst case and the row is a translation defect.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 62, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq"],
//     "loop_depth": 2, "loops": 3, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1105_B. Zuhair and Strings  (problem 2231, solution 2231_77)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k = int(input().split()[1])
// result = {}
// prev = 0
// value = 0
// STR = input() + '$'
// 
// for letter in STR:
//     if letter != prev:
//         result[prev] = result.get(prev, 0) + value//k
//         prev = letter
//         value = 0
//     value+=1
// 
// print(max(result.values()))  
// --------------------------------------------------------------------

include "../../prelude.dfy"

lemma Sq2231(N: nat, K: nat)
  requires K == 13 * N + 14
  ensures N * K == 13 * (N * N) + 14 * N
{
}

method Solve(a: int, b: int, string_: string)
    returns (output: string, ghost steps: nat)
  requires b >= 1
  requires |string_| >= 1 ==> string_[0] != '\0'
  ensures steps <= 13 * ((|string_| + 1) * (|string_| + 1)) + 24 * (|string_| + 1) + 5 + |output|
{
  steps := 0;
  ghost var N := |string_| + 1;
  ghost var K: nat := 13 * N + 14;
  var k := b;
  steps := steps + |"$"|;
  var strSeq := string_ + "$";
  var entries: seq<(char, int)> := [];
  var prev := '\0';
  var value := 0;
  var i := 0;
  while i < |strSeq|
    invariant 0 <= i <= |strSeq|
    invariant |strSeq| == |string_| + 1
    invariant strSeq[0] != '\0'
    invariant i == 0 ==> prev == '\0'
    invariant i >= 1 ==> |entries| >= 1
    invariant |entries| <= i
    invariant steps <= 1 + i * K
    decreases |strSeq| - i
  {
    ghost var s_out := steps;
    steps := steps + 3;
    steps := steps + 1;
    var letter := strSeq[i];
    assert i == 0 ==> letter != prev;
    steps := steps + 1;
    if letter != prev {
      steps := steps + 1;
      var addition := FloorDiv(value, k);
      var found := false;
      var newEntries: seq<(char, int)> := [];
      var j := 0;
      ghost var s0 := steps;
      while j < |entries|
        invariant 0 <= j <= |entries|
        invariant |newEntries| == j
        invariant found ==> j >= 1
        invariant steps <= s0 + 13 * j
        decreases |entries| - j
      {
        steps := steps + 3;
        steps := steps + 3;
        if entries[j].0 == prev {
          steps := steps + (5 + |[(prev, entries[j].1 + addition)]|);
          newEntries := newEntries + [(prev, entries[j].1 + addition)];
          found := true;
        } else {
          steps := steps + (2 + |[entries[j]]|);
          newEntries := newEntries + [entries[j]];
        }
        steps := steps + 1;
        j := j + 1;
      }
      steps := steps + 2;
      steps := steps + 1;
      if !found {
        steps := steps + (2 + |[(prev, addition)]|);
        newEntries := newEntries + [(prev, addition)];
      }
      assert |newEntries| >= 1;
      entries := newEntries;
      prev := letter;
      value := 0;
    }
    steps := steps + 1;
    value := value + 1;
    steps := steps + 1;
    assert steps <= s_out + 14 + 13 * i;
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
  }
  steps := steps + 2;
  Sq2231(N, K);
  ghost var B := steps;
  var vals: seq<int> := [];
  var j2 := 0;
  while j2 < |entries|
    invariant 0 <= j2 <= |entries|
    invariant |vals| == j2
    invariant steps <= B + 9 * j2
    decreases |entries| - j2
  {
    steps := steps + 3;
    steps := steps + (3 + |[entries[j2].1]|);
    vals := vals + [entries[j2].1];
    steps := steps + 1;
    j2 := j2 + 1;
  }
  steps := steps + 2;
  steps := steps + (|vals| + Digits(MaxSeq(vals)));
  IntToStringDigits(MaxSeq(vals));
  output := IntToString(MaxSeq(vals));
}

import opened Prelude
