// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(nlogn)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-06
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python uses Counter and linear loops so it is O(n) as labelled,
//     but the Dafny sorts with SortInts (O(n log n)) and then
//     binary-searches `distinct` for each of the n elements, so its class
//     is O(n log n); the sort/binary search replaces the hash count.
//
//   how this label could be wrong, and what to check:
//     The label O(n) matches the Python, which counts with
//     collections.Counter in one pass. Open the Dafny and check for
//     `SortInts(numbers)` at the top and the per-element binary search
//     over `distinct` in the final loop; either makes it O(n log n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 65, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     5, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": ["SortInts"], "uses_map": false, "uses_multiset":
//     false, "uses_set": false}
// --------------------------------------------------------------------

// 1051_C. Vasya and Multisets  (problem 2005, solution 2005_137)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// n = int(input())
// s = list(map(int,input().split()))
// c = Counter(s)
// singles = [i for i in c if c[i]==1]
// multis = [i for i in c if c[i]>2]
// if len(singles)&1 and not multis:
//     print("NO")
// else:
//     print("YES")
//     sin,mul=len(singles)//2,len(singles)&1
//     ans = ""
//     for x in s:
//         if mul and c[x]>2:
//             mul-=1
//             ans+="A"
//         elif sin and c[x]==1:
//             sin-=1
//             ans+="A"
//         else:ans+="B"
//     print(ans)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var c: map<int, int> := map[];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
  {
    var v := numbers[i];
    c := c[v := (if v in c then c[v] else 0) + 1];
    i := i + 1;
  }
  var singlesCount := 0;
  var multisNonEmpty := false;
  var keys := c.Keys;
  while keys != {}
    invariant keys <= c.Keys
    decreases |keys|
  {
    var key :| key in keys;
    if c[key] == 1 { singlesCount := singlesCount + 1; }
    if c[key] > 2 { multisNonEmpty := true; }
    keys := keys - {key};
  }
  if singlesCount % 2 == 1 && !multisNonEmpty {
    output := "NO\n";
  } else {
    var sin := singlesCount / 2;
    var mul := singlesCount % 2;
    var ansParts: seq<string> := [];
    var m := 0;
    while m < |numbers|
    {
      var x := numbers[m];
      var cx := if x in c then c[x] else 0;
      if mul > 0 && cx > 2 {
        mul := mul - 1;
        ansParts := ansParts + ["A"];
      } else if sin > 0 && cx == 1 {
        sin := sin - 1;
        ansParts := ansParts + ["A"];
      } else {
        ansParts := ansParts + ["B"];
      }
      m := m + 1;
    }
    output := "YES\n" + Join(ansParts, "") + "\n";
  }
}
