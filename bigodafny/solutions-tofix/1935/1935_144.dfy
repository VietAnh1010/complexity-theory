// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)log(n+m)
//   audited class  : O(n+mlogm)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-13
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The scan 'while i<|s|' building kiri/tupl is a plain O(n) pass with
//     O(1) amortised appends, and SortInts is called only on 'ini' whose
//     length is capped by m via 'tupl[..take]' with take<=m/2, so the true
//     cost is O(n+m log m), a smaller class than the labelled
//     O((n+m)log(n+m)).
//
//   how this label could be wrong, and what to check:
//     The label O((n+m)log(n+m)) implies the entire string of length n
//     gets sorted. Check that SortInts is called only on 'ini', whose size
//     is bounded by m via 'tupl:=tupl[..take]' with take<=m/2, and that
//     the earlier scan of s is a single unsorted O(n) pass; if so the sort
//     contributes m log m, not (n+m) log(n+m).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 56, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 3,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": ["SortInts"], "uses_map": false, "uses_multiset":
//     false, "uses_set": false}
// --------------------------------------------------------------------

// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_144)
// time complexity: O(n+m)log(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// aa,bb=map(int, input().split())
// s=input()
// kiri=[]
// tupl=[]
// ini=[]
// cetak=""
// for i in range(len(s)):
// 	if s[i]=="(":
// 		kiri.append(i)
// 	else:
// 		tupl.append((kiri.pop(),i))
// tupl=tupl[:bb//2]
// for k in tupl:
// 	ini.extend(k)
// ini.sort()
// for j in ini:
// 	cetak+=s[j]
// print(cetak)
// 			   	 	   	  		 	 	 		 				 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
  // kiri holds one entry per '(' and loses one per other character, so
  // |kiri| == 2*Opens(s,i) - i. The pop is safe exactly when that is positive.
  // Stated over non-'(' characters rather than over ')' because 6 stored
  // inputs contain neither bracket and the row's Python handles them.
  requires forall t :: 0 <= t < |s| && s[t] != '(' ==> 2 * Opens(s, t) > t
{
  var kiri: seq<int> := [];
  var tupl: seq<(int,int)> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |kiri| == 2 * Opens(s, i) - i
    invariant forall t :: 0 <= t < |kiri| ==> 0 <= kiri[t] < |s|
    invariant forall t :: 0 <= t < |tupl| ==> 0 <= tupl[t].0 < |s| && 0 <= tupl[t].1 < |s|
    decreases |s| - i
  {
    if s[i] == '(' {
      var kiri' := kiri + [i];
      assert forall t :: 0 <= t < |kiri'| ==>
        kiri'[t] == (if t < |kiri| then kiri[t] else i);
      kiri := kiri';
    } else {
      assert 2 * Opens(s, i) > i;
      assert |kiri| >= 1;
      tupl := tupl + [(kiri[|kiri|-1], i)];
      kiri := kiri[..|kiri|-1];
    }
    i := i + 1;
  }
  var take := if m/2 <= |tupl| then m/2 else |tupl|;
  if take < 0 { take := 0; }
  tupl := tupl[..take];
  var ini: seq<int> := [];
  var k := 0;
  while k < |tupl|
    invariant 0 <= k <= |tupl|
    invariant forall x :: x in ini ==> 0 <= x < |s|
    decreases |tupl| - k
  {
    ini := ini + [tupl[k].0, tupl[k].1];
    k := k + 1;
  }
  SortIntsKeepsElems(ini);
  ini := SortInts(ini);
  var cetak := "";
  var j := 0;
  while j < |ini|
    invariant 0 <= j <= |ini|
    invariant forall x :: x in ini ==> 0 <= x < |s|
    decreases |ini| - j
  {
    assert ini[j] in ini;
    cetak := cetak + [s[ini[j]]];
    j := j + 1;
  }
  output := cetak + "\n";
}
