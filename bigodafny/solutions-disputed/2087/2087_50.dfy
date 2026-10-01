// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-06
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python's a=a[1:] copies on each iteration and is quadratic per
//     string, but the Dafny's slice views and O(1) appends make the peel
//     loop O(len), and the rev/alphabet scan is bounded by the literal
//     26-letter alphabet, so total cost is linear in the input; this is
//     the slicing shape.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) was measured on a Python that peels with `a =
//     a[1:]`, which copies the remaining string each step and is quadratic
//     in the string length. Check the Dafny: it peels with `a := a[1..]`
//     and `a[..|a|-1]`, which are O(1) views, and appends with `s + [x]`
//     (O(1) amortised), so the same loop is linear.
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
