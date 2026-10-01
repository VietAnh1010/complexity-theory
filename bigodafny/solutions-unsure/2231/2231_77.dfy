// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : low
//   auditor        : labelaudit-r3-13
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     On each run boundary the Dafny scans and rebuilds the whole
//     `entries` seq (inner loop j over |entries|) where the Python does
//     one dict get and set; entries is bounded only by the number of
//     distinct characters, which the source does not cap, so the cost is
//     O(runs * distinct) rather than O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the Python dict result is O(1) per key. The Dafny
//     replaces it with a seq of (char,int) pairs rebuilt by the inner
//     `while j < |entries|` loop at every run flush. Check whether the
//     number of distinct keys in `entries` can be treated as constant: the
//     statement says lowercase letters, but the Dafny has no requires
//     bounding the alphabet, so the inner loop is up to n long. If the
//     26-letter cap is accepted as a fixed constant the label stands; if
//     not, the row is O(n*d).
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
import opened Prelude

method Solve(a: int, b: int, string_: string) returns (output: string)
  // the sentinel run is flushed on the first character, which is never NUL
  requires b >= 1
  requires |string_| >= 1 ==> string_[0] != '\0'
{
  var k := b;
  var strSeq := string_ + "$";
  var entries: seq<(char,int)> := [];
  var prev := '\0';
  var value := 0;
  var i := 0;
  while i < |strSeq|
    invariant 0 <= i <= |strSeq|
    invariant |strSeq| == |string_| + 1
    invariant strSeq[0] != '\0'
    invariant i == 0 ==> prev == '\0'
    invariant i >= 1 ==> |entries| >= 1
    decreases |strSeq| - i
  {
    var letter := strSeq[i];
    assert i == 0 ==> letter != prev;
    if letter != prev {
      var addition := FloorDiv(value, k);
      var found := false;
      var newEntries: seq<(char,int)> := [];
      var j := 0;
      while j < |entries|
        invariant 0 <= j <= |entries|
        invariant |newEntries| == j
        invariant found ==> j >= 1
        decreases |entries| - j
      {
        if entries[j].0 == prev {
          newEntries := newEntries + [(prev, entries[j].1 + addition)];
          found := true;
        } else {
          newEntries := newEntries + [entries[j]];
        }
        j := j + 1;
      }
      if !found { newEntries := newEntries + [(prev, addition)]; }
      assert |newEntries| >= 1;
      entries := newEntries;
      prev := letter;
      value := 0;
    }
    value := value + 1;
    i := i + 1;
  }
  var vals: seq<int> := [];
  var j2 := 0;
  while j2 < |entries|
    invariant 0 <= j2 <= |entries|
    invariant |vals| == j2
    decreases |entries| - j2
  {
    vals := vals + [entries[j2].1];
    j2 := j2 + 1;
  }
  output := IntToString(MaxSeq(vals));
}
