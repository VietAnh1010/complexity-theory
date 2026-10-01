// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : harness
//   confidence     : medium
//   auditor        : labelaudit-r4-u01
//
//   Both artifacts are right. The Python pays to parse stdin and
//   BigOBench profiled the whole script; the Dafny's Solve receives the
//   inputs already parsed, so that cost is outside the measured method.
//   Nothing to repair -- document it.
//
//   evidence:
//     Solve's single loop runs to |a| and reads b only by index and
//     length, so it is O(n); the Python pays list(b) as a full O(m)
//     conversion that the Dafny, taking b as an already-built string,
//     never performs, so the label is right for the Python and the Dafny
//     is right for its boundary.
//
//   how this label could be wrong, and what to check:
//     The label O(n+m) assumes both strings are scanned. In Solve only `a`
//     is walked (`while i < n` with n := |a|) and b is touched by |b| and
//     b[i]; if the lengths differ the loop exits on the first iteration.
//     The Python does list(a) and list(b), converting both strings. Check
//     whether you count that list(b) copy as the cost the Dafny dropped.
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
