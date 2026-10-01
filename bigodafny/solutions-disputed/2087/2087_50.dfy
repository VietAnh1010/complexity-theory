// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python's a=a[1:] copies the rest of the string on every step, so
//     each test is quadratic in its length, as the label says. The Dafny's
//     `a := a[1..]` is an O(1) view and `s := s + [c]` is amortised O(1),
//     and the alphabet window loop has a literal bound of 26, so each of n
//     strings costs O(m) and the total is O(n*m): the slicing shape, one
//     class faster than the Python.
//
//   how this label could be wrong, and what to check:
//     The label was measured on a Python that peels the string with `a =
//     a[1:]`, which copies and is quadratic in the string length. Check
//     that the Dafny peels with `a := a[1..]` (a view) and rebuilds s by
//     appending one character; if so each string costs O(m), not O(m**2).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 47, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     3, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1547_B. Alphabetical Strings  (problem 2087, solution 2087_50)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for _ in range(int(input())):
//     a=input()
//     s=""
//     while  len(a)!=1:
//         if a[0]>a[-1]:
//             s+=a[0]
//             a=a[1:]
//         else:
//             s+=a[-1]
//             a=a[:-1]
// 
//         if len(a)==1:
//             break
//     s+="a"
//     if a!="a" or s[::-1] not in "abcdefghijklmnopqrstuvwxyz":
//         print("NO")
//     else:
//         print("YES")
//             
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(strings: seq<string>) returns (output: string)
  requires forall k :: 0 <= k < |strings| ==> |strings[k]| >= 1
{
  var alphabet := "abcdefghijklmnopqrstuvwxyz";
  var results: seq<string> := [];
  var si := 0;
  while si < |strings|
    decreases |strings| - si
  {
    var a := strings[si];
    var s := "";
    while |a| != 1
      invariant |a| >= 1
      decreases |a|
    {
      if a[0] > a[|a| - 1] {
        s := s + [a[0]];
        a := a[1..];
      } else {
        s := s + [a[|a| - 1]];
        a := a[..|a| - 1];
      }
    }
    s := s + "a";
    var rev: string := seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i]);
    var found := false;
    var start := 0;
    while start + |rev| <= |alphabet| && !found
      invariant 0 <= start <= |alphabet|
      decreases |alphabet| - start
    {
      if alphabet[start..start + |rev|] == rev {
        found := true;
      }
      start := start + 1;
    }
    if a != "a" || !found {
      results := results + ["NO"];
    } else {
      results := results + ["YES"];
    }
    si := si + 1;
  }
  output := Join(results, "\n");
}
