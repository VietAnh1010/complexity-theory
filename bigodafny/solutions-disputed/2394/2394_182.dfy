// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-18
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny never calls a sort; it maintains sndOk with one O(1)
//     comparison sndLast > s[i] per loop iteration and writes into a real
//     array (O(1) per write), so the whole loop is O(n), whereas the
//     Python builds snd_lst then calls sorted(snd_lst) and compares, an
//     O(n log n) operation.
//
//   how this label could be wrong, and what to check:
//     The label assumes the sndOk check re-sorts snd_lst as Python's
//     sorted(snd_lst)==snd_lst does. Open the Dafny loop and confirm sndOk
//     is tracked incrementally via a single sndLast>s[i] comparison per
//     iteration, with no SortStrings/SortInts call anywhere; if so the
//     Dafny never sorts and is O(n), while the label was measured on the
//     Python's O(n log n) sort.
//
//   structural facts (deterministic, from labelaudit.py):
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
