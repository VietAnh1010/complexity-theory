// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny recounts s[i] against all of s for each i with two nested
//     loops over |s|, which is O(n**2). The Python builds `count` in one
//     pass and scans at most 26 keys, so it is O(n) as labelled; the
//     translation replaced the dict with a rescan, which is the
//     algorithm-replaced shape.
//
//   how this label could be wrong, and what to check:
//     The label matches the Python's single-pass dict count. Check whether
//     the Dafny's nested `while i < |s|` / `while j < |s|` loops recount
//     every character from scratch; if so it is quadratic while the
//     Python's `count` dict is linear.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 2, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 841_A. Generous Kefa  (problem 2853, solution 2853_327)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=list(map(int,input().split()))
// s=input()
// count={}
// for val in s:	
// 	if(val not in count):
// 		count[val]=0
// 	count[val]+=1
// flag=0
// for item in count:
// 	if(count[item]>m):
// 		flag=1
// 		break
// if(flag==0):
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string)
{
  var count: map<char, int> := map[];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    decreases |s| - i
  {
    var val := s[i];
    if val !in count {
      count := count[val := 0];
    }
    count := count[val := count[val] + 1];
    i := i + 1;
  }
  var flag := false;
  var ks := count.Keys;
  while ks != {} && !flag
    invariant ks <= count.Keys
    decreases |ks|
  {
    var item :| item in ks;
    if count[item] > k {
      flag := true;
    }
    ks := ks - {item};
  }
  if flag {
    output := "NO";
  } else {
    output := "YES";
  }
}
