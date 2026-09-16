// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(nlogn)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-14
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     SortInts(numbers) costs O(n log n) per the prelude table, and the
//     loop `while m < |numbers|` runs a binary search over distinct on
//     every iteration, adding O(n log n) more, whereas the Python's
//     Counter gives O(1) lookups for an overall O(n) pass.
//
//   how this label could be wrong, and what to check:
//     The label assumes O(1) frequency lookups as Python's Counter gives;
//     the Dafny instead calls SortInts (O(n log n) per the cost table) and
//     then runs a binary search over `distinct` inside the final while
//     loop over m, adding another O(n log n). Confirm SortInts appears and
//     that the final loop's binary search (`while lo < hi`) executes once
//     per element of numbers.
//
//   structural facts (deterministic, from labelaudit.py):
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
  var sorted := SortInts(numbers);
  var distinct: seq<int> := [];
  var counts: seq<int> := [];
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |distinct| == |counts|
  {
    var v := sorted[i];
    var j := i;
    while j < |sorted| && sorted[j] == v
      invariant i <= j <= |sorted|
    { j := j + 1; }
    distinct := distinct + [v];
    counts := counts + [j - i];
    i := j;
  }
  var singlesCount := 0;
  var multisNonEmpty := false;
  var k := 0;
  while k < |counts|
  {
    if counts[k] == 1 { singlesCount := singlesCount + 1; }
    if counts[k] > 2 { multisNonEmpty := true; }
    k := k + 1;
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
      var lo := 0;
      var hi := |distinct|;
      while lo < hi
        invariant 0 <= lo <= hi <= |distinct|
      {
        var mid := (lo + hi) / 2;
        if distinct[mid] == x { lo := mid; hi := mid; }
        else if distinct[mid] < x { lo := mid + 1; }
        else { hi := mid; }
      }
      var cx := if lo < |distinct| && distinct[lo] == x then counts[lo] else 0;
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
