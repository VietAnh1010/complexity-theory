// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     `Signature619` is O(|s|) per word, O(n*m) in all, but
//     `CountDistinct619` keeps `seen` as a seq and tests membership by
//     scanning it, O(n**2) for distinct roots, so the Dafny is O(n*m +
//     n**2); the Python's dict is O(n*m).
//
//   how this label could be wrong, and what to check:
//     Two faults. The Python's `l2.sort()` sorts at most 26 distinct
//     letters, a constant, and its dict makes the count O(n*m) over n
//     words of length m, so the n log n label names nothing. The Dafny's
//     `CountDistinct619` tests `xs[i] !in seen` against a seq, a linear
//     scan, so n distinct roots cost O(n**2). Check the type of `seen`.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 58, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 975_A. Aramic script  (problem 619, solution 619_340)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = list(input().split())
// dic = dict()
// for i in s:
//     l2 = list(set(list(i)))
//     l2.sort()
//     l2 = ''.join(l2)
//     if l2 in dic:
//         pass
//     else:
//         dic[l2] = 1
// c = 0
// #print(dic)
// for i in dic:
//     c+=1
// print(c)
//     
//         
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var sigs: seq<string> := [];
  var i := 0;
  while i < |strings|
    decreases |strings| - i
  {
    var sg := Signature619(strings[i]);
    sigs := sigs + [sg];
    i := i + 1;
  }
  var distinctCount := CountDistinct619(sigs);
  output := IntToString(distinctCount);
}

method Signature619(s: string) returns (sig: string)
{
  var pres := seq(26, _ => false);
  var i := 0;
  while i < |s|
    invariant |pres| == 26
    decreases |s| - i
  {
    var idx := (s[i] as int) - ('a' as int);
    if 0 <= idx < 26 {
      pres := pres[idx := true];
    }
    i := i + 1;
  }
  var alphabet := "abcdefghijklmnopqrstuvwxyz";
  sig := "";
  i := 0;
  while i < 26
    invariant 0 <= i <= 26
    invariant |pres| == 26
    decreases 26 - i
  {
    if pres[i] {
      sig := sig + [alphabet[i]];
    }
    i := i + 1;
  }
}

method CountDistinct619(xs: seq<string>) returns (c: int)
{
  var seen: seq<string> := [];
  var i := 0;
  while i < |xs|
    decreases |xs| - i
  {
    if xs[i] !in seen {
      seen := seen + [xs[i]];
    }
    i := i + 1;
  }
  c := |seen|;
}
