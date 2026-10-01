// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : harness
//   confidence     : low
//   auditor        : labelaudit-r3-14
//
//   Both artifacts are right. The Python pays to parse stdin and
//   BigOBench profiled the whole script; the Dafny's Solve receives the
//   inputs already parsed, so that cost is outside the measured method.
//   Nothing to repair -- document it.
//
//   evidence:
//     The while loop in Solve runs i up to n=|a| and breaks at once when n
//     != |b|, indexing b[i] only while |b| == n, so it is O(n); the O(n+m)
//     label only matches the Python, which converts both strings with
//     list(a) and list(b).
//
//   how this label could be wrong, and what to check:
//     The label assumes the second string b is scanned. In the Dafny, b is
//     read only as b[i] for i < n=|a| and only when |b| == n, so m never
//     adds cost beyond n. Compare the Python's `b=list(b)` (O(m)
//     parse/copy) with the Dafny that takes b as a ready string. If the
//     two strings are treated as halves of one input the label is a naming
//     choice and is ok; if not, it is a harness gap.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 35, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1111_A. Superhero Transformation  (problem 2436, solution 2436_325)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// cons=['b', 'c', 'd','f', 'g', 'h', 'j', 'k', 'l', 'm', 'n', 'p', 'q', 'r', 's', 't','v', 'w', 'x', 'y', 'z']
// vow=['a','e','i','o','u']
// a=input()
// b=input()
// n=len(a)
// a=list(a)
// b=list(b)
// i=0
// while(i<n): 
//     if (n!=len(b)):
//         print('No')
//         break
//     if ((a[i] in cons) and (b[i] in vow)) or ((a[i] in vow) and (b[i] in cons)):
//         print("No")
//         break
//     i=i+1
// if (i==n):
//     print("Yes")
// 
//                     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

predicate IsVowel(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

predicate IsCons(c: char)
{
  'a' <= c <= 'z' && !IsVowel(c)
}

method Solve(a: string, b: string) returns (output: string)
{
  var n := |a|;
  var i := 0;
  var broke := false;
  while i < n && !broke
    invariant 0 <= i <= n
    decreases n - i, (if broke then 0 else 1)
  {
    if n != |b| {
      broke := true;
    } else if (IsCons(a[i]) && IsVowel(b[i])) || (IsVowel(a[i]) && IsCons(b[i])) {
      broke := true;
    } else {
      i := i + 1;
    }
  }
  if broke {
    output := "No\n";
  } else if i == n {
    output := "Yes\n";
  } else {
    output := "";
  }
}
