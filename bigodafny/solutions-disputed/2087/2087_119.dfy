// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-s03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over every string in `strings` and the inner while loop
//     peels r with r[1..] or r[..|r|-1] once per character (up to |r|
//     steps), so it scans each of the n strings once: O(n*m) in the string
//     count and string length, not O(n). The Python's recursive
//     alpha(r[1:], ...) also walks each string, and copies on each slice,
//     so it is no better.
//
//   how this label could be wrong, and what to check:
//     The label O(n) treats each string as constant width. Check the inner
//     `while !done` loop: it runs once per character of r, i.e. up to
//     |strings[k]| times. The statement caps length at 26 but that cap is
//     not a source literal; if the dataset decides a 26-letter alphabet is
//     a constant the label stands, otherwise it should be O(n*m).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 43, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     2, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1547_B. Alphabetical Strings  (problem 2087, solution 2087_119)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = "abcdefghijklmnopqrstuvwxyz"
// def alpha (r,n):
//     if len(r)==1 and r[0]==n:
//         print("YES")
//         return 0
//     elif r[0]==n:
//         alpha(r[1:],a[(a.find(n))-1])
//     elif r[-1]==n:
//          alpha(r[:-1],a[(a.find(n))-1])
//     else:
//         print("NO")
// k = int(input())
// for i in range(k):
//     r = str(input())
//     alpha(r,a[len(r)-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(strings: seq<string>) returns (output: string)
  requires forall k :: 0 <= k < |strings| ==> 1 <= |strings[k]| <= 26
{
  var results: seq<string> := [];
  var si := 0;
  while si < |strings|
    decreases |strings| - si
  {
    var r := strings[si];
    var idxLetter := |r| - 1;
    var res := "";
    var done := false;
    while !done
      invariant 1 <= |r| <= 26
      invariant idxLetter == |r| - 1
      decreases !done, |r|
    {
      var n := (('a' as int) + idxLetter) as char;
      if |r| == 1 {
        if r[0] == n {
          res := "YES";
        } else {
          res := "NO";
        }
        done := true;
      } else if r[0] == n {
        r := r[1..];
        idxLetter := idxLetter - 1;
      } else if r[|r| - 1] == n {
        r := r[..|r| - 1];
        idxLetter := idxLetter - 1;
      } else {
        res := "NO";
        done := true;
      }
    }
    results := results + [res];
    si := si + 1;
  }
  output := Join(results, "\n");
}
