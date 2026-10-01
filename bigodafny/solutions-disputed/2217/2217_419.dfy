// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r4-d03
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python's dict d gives O(1) get, set and pop per request, so it
//     is O(n). The Dafny replaced the map with parallel seqs keys and vals
//     and does three `while ... < |keys|` linear scans per handle (fi, fj,
//     fk) and a keys[..popIdx] + keys[popIdx+1..] rebuild, so each of n
//     requests costs O(|keys|) and the total is O(n**2). A hash lookup
//     became a linear search, which is an algorithm change, not a
//     container-update difference.
//
//   how this label could be wrong, and what to check:
//     The label was measured on a Python that keeps the handle map in a
//     dict (O(1) lookups). Check that the Dafny holds keys and vals in two
//     seqs and runs three linear scans per request (fi, fj, fk loops) plus
//     slice-and-concatenate on removal.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 63, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "SplitWs"],
//     "loop_depth": 2, "loops": 5, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": true, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 501_B. Misha and Changing Handles  (problem 2217, solution 2217_419)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// d = {}
// for i in range(t):
//     old,new = input().split()
//     d[new] = d.get(old,old)
//     if old in d:
//     	d.pop(old)
// print(len(d))
// for a,b in d.items():
//     print(b,a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, handles: seq<string>) returns (output: string)
{
  var keys: seq<string> := [];
  var vals: seq<string> := [];
  var i := 0;
  while i < |handles|
    invariant 0 <= i <= |handles|
    invariant |keys| == |vals|
  {
    var parts := SplitWs(handles[i]);
    var oldh := if |parts| >= 1 then parts[0] else "";
    var newh := if |parts| >= 2 then parts[1] else "";
    var oldIdx := -1;
    var fi := 0;
    while fi < |keys|
      invariant 0 <= fi <= |keys|
      invariant oldIdx == -1 || (0 <= oldIdx < fi)
    {
      if keys[fi] == oldh { oldIdx := fi; }
      fi := fi + 1;
    }
    var val := if oldIdx == -1 then oldh else vals[oldIdx];
    var newIdx := -1;
    var fj := 0;
    while fj < |keys|
      invariant 0 <= fj <= |keys|
      invariant newIdx == -1 || (0 <= newIdx < fj)
    {
      if keys[fj] == newh { newIdx := fj; }
      fj := fj + 1;
    }
    if newIdx == -1 {
      keys := keys + [newh];
      vals := vals + [val];
    } else {
      vals := vals[newIdx := val];
    }
    var popIdx := -1;
    var fk := 0;
    while fk < |keys|
      invariant 0 <= fk <= |keys|
      invariant popIdx == -1 || (0 <= popIdx < fk)
    {
      if keys[fk] == oldh { popIdx := fk; }
      fk := fk + 1;
    }
    if popIdx != -1 {
      keys := keys[..popIdx] + keys[popIdx+1..];
      vals := vals[..popIdx] + vals[popIdx+1..];
    }
    i := i + 1;
  }
  var parts2: seq<string> := [];
  var m := 0;
  while m < |keys|
  {
    parts2 := parts2 + [vals[m] + " " + keys[m]];
    m := m + 1;
  }
  output := IntToString(|keys|) + "\n" + (if |parts2| == 0 then "" else Join(parts2, "\n") + "\n");
}
