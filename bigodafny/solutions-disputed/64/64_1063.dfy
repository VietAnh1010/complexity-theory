// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny prepends with `listt := [v] + listt`, a concatenation
//     charged |listt| <= k per new id, so the loop over ratings is O(n*k);
//     the Python uses deque.appendleft and pop, both O(1), and is O(n) as
//     labelled.
//
//   how this label could be wrong, and what to check:
//     The label holds for the Python, whose deque.appendleft is O(1).
//     Check the Dafny's `listt := [v] + listt` and `[v] + listt[..|listt|
//     - 1]`: a prepend is a concat charged |listt| (up to k), so each new
//     id costs O(k). If the Dafny appended instead, it would be O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 29, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "JoinInts"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": true, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": true}
// --------------------------------------------------------------------

// 1234_B1. Social Network (easy version)  (problem 64, solution 64_1063)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import deque
// n,k=map(int,input().split())
// inp=list(map(int,input().split()))
// listt=deque()
// dictt={}
// for i in inp:
// 	dictt[i]=False
// for i in inp:
// 	if len(listt)<k:
// 		if  dictt[i]==False:
// 			listt.appendleft(i)
// 			# listt=[i]+listt
// 			dictt[i]=True
// 	if len(listt)==k:
// 		if dictt[i]==False:
// 			dictt[i]=True
// 			dictt[listt[-1]]=False
// 			# listt=[i]+listt
// 			listt.appendleft(i)
// 			# listt=listt[:-1]
// 			listt.pop()
// 	# print(listt)
// 	# print(dictt)
// 
// print(len(listt))
// print(*listt)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, ratings: seq<int>) returns (output: string)
  requires k >= 1
{
  var listt: seq<int> := [];
  var present: set<int> := {};
  var idx := 0;
  while idx < |ratings|
    decreases |ratings| - idx
  {
    var v := ratings[idx];
    if |listt| < k {
      if v !in present {
        listt := [v] + listt;
        present := present + {v};
      }
    }
    if |listt| == k {
      if v !in present {
        present := present - {listt[|listt| - 1]};
        present := present + {v};
        listt := [v] + listt[..|listt| - 1];
      }
    }
    idx := idx + 1;
  }
  output := IntToString(|listt|) + "\n" + JoinInts(listt, " ");
}
