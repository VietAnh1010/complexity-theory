// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-17
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The while loop over a_list performs freq := freq[v := c] every
//     iteration, a Dafny map<string,int> update that copies the whole map
//     per the cost table, giving O(1+2+...+n)=O(n**2) total, while
//     Python's Counter(num) plus a single pass over its keys is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes freq := freq[v := c] is an O(1) dict write as in
//     Python's Counter. Open the loop and confirm the map update is a
//     Dafny `map` (m[k := v]), which the table scores O(|m|) per write
//     (full copy) -- summed over n iterations that is O(n**2), unlike
//     Python's collections.Counter which mutates in place in O(1)
//     amortized.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 22, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": true, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 296_A. Yaroslav and Permutations  (problem 2266, solution 2266_298)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # your code goes here
// n=int(input())
// num=map(int,input().split())
// from collections import Counter
// freq=Counter(num)
// maximum=0
// for i in freq:
// 	if(maximum<freq[i]):
// 		maximum=freq[i]
// if(maximum <=((n+1)//2)):
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var freq: map<string, int> := map[];
  var maximum := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    var c := if v in freq then freq[v] + 1 else 1;
    freq := freq[v := c];
    if c > maximum { maximum := c; }
    i := i + 1;
  }
  if maximum <= (n + 1) / 2 {
    output := "YES";
  } else {
    output := "NO";
  }
}
