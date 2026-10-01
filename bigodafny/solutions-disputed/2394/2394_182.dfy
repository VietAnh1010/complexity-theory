// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-07
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python sorts snd_lst (up to n elements) to test it is
//     non-decreasing, which is O(n log n) as labelled, while the Dafny
//     replaces that with a one-pass `haveSnd && sndLast > s[i]` check in a
//     single loop over m, so Solve is O(n). That is an algorithm
//     replacement (a sort dropped), landing in a better class than the
//     labelled Python.
//
//   how this label could be wrong, and what to check:
//     The label's n log n comes from the Python's
//     `sorted(snd_lst)==snd_lst`; the Dafny has no sort. Compare the
//     Python's final sorted() check against the Dafny's running
//     sndLast/sndOk comparison inside the single loop; if the Dafny still
//     sorted anywhere the label would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 36, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1296_E1. String Coloring (easy version)  (problem 2394, solution 2394_182)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n = int(input())
//     s = input()
//     fst_lst = [s[0]]
//     snd_lst = []
//     ans = '1'
//     for i in range(1, len(s)):
//         if fst_lst[-1]<=s[i]:
//             fst_lst.append(s[i])
//             ans+='1'
//         else:
//             snd_lst.append(s[i])
//             ans+='0'
//     # print (*fst_lst)
//     # print (*snd_lst)
//     if sorted(snd_lst)==snd_lst:
//         print ('YES')
//         print (ans)
//     else:
//         print ('NO')
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_: string) returns (output: string)
  requires |string_| >= 1
{
  var s := string_;
  var m := |s|;
  var ans := new char[m];
  ans[0] := '1';
  var fstLast := s[0];
  var sndOk := true;
  var haveSnd := false;
  var sndLast := s[0];
  var i := 1;
  while i < m
    invariant 1 <= i <= m
  {
    if fstLast <= s[i] {
      fstLast := s[i];
      ans[i] := '1';
    } else {
      if haveSnd && sndLast > s[i] {
        sndOk := false;
      }
      sndLast := s[i];
      haveSnd := true;
      ans[i] := '0';
    }
    i := i + 1;
  }
  if sndOk {
    output := "YES\n" + ans[..] + "\n";
  } else {
    output := "NO\n";
  }
}
