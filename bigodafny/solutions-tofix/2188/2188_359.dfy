// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-16
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The final loop over dif executes difmax := difmax[s := difmax[s] +
//     1], a seq functional update inside a loop of n iterations, costing
//     O(n) per update and O(n**2) total for that loop, which dominates the
//     two O(n log n) Sort calls; the Python's difmax[s]+=1 is an O(1) list
//     index write, so the Python is O(n log n) as labelled.
//
//   how this label could be wrong, and what to check:
//     The label assumes difmax updates are O(1) as in Python's list. Check
//     whether difmax is a Dafny seq with a functional update `difmax :=
//     difmax[s := difmax[s] + 1]` inside the loop over n elements; if so,
//     per the cost table each update is O(|difmax|)=O(n), making that loop
//     alone O(n**2), dominating the two O(n log n) sorts.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 60, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": ["Sort"], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1365_C. Rotation Matching  (problem 2188, solution 2188_359)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int,input().split()))
// b = list(map(int,input().split()))
// dif = [0]*n
// a = list(enumerate(a))
// b = list(enumerate(b))
// a.sort(key = lambda x:x[1])
// b.sort(key = lambda x:x[1])
// for i in range(n):
//     q1 = a[i][0]
//     q2 = b[i][0]
//     if q2-q1<0:
//         dif[i]=(n+(q2-q1))
//     else:
//         dif[i]=(q2-q1)
// maxi = 0
// difmax = [0]*n
// for s in dif:
//     difmax[s]+=1
//     if difmax[s]>maxi:
//         maxi = difmax[s]
// print(maxi)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
  requires n >= 1
  requires |a_list| == n
  requires |b_list| == n
{
  var aPairs: seq<(int,int)> := [];
  var bPairs: seq<(int,int)> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |aPairs| == i
    invariant |bPairs| == i
    invariant forall k :: 0 <= k < i ==> aPairs[k].0 == k
    invariant forall k :: 0 <= k < i ==> bPairs[k].0 == k
    decreases n - i
  {
    aPairs := aPairs + [(i, a_list[i])];
    bPairs := bPairs + [(i, b_list[i])];
    i := i + 1;
  }
  var aSorted := Sort(aPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  var bSorted := Sort(bPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  SortKeepsElems(aPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  SortKeepsElems(bPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  assert forall p :: p in aPairs ==> 0 <= p.0 < n;
  assert forall p :: p in bPairs ==> 0 <= p.0 < n;
  var dif: seq<int> := [];
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |dif| == i
    invariant forall k :: 0 <= k < i ==> 0 <= dif[k] < n
    decreases n - i
  {
    assert aSorted[i] in aSorted;
    assert bSorted[i] in bSorted;
    var q1 := aSorted[i].0;
    var q2 := bSorted[i].0;
    var d := if q2 - q1 < 0 then n + (q2 - q1) else q2 - q1;
    dif := dif + [d];
    i := i + 1;
  }
  var difmax := seq(if n >= 0 then n else 0, _ => 0);
  var maxi := 0;
  i := 0;
  while i < |dif|
    invariant 0 <= i <= |dif|
    invariant |difmax| == n
    invariant forall k :: 0 <= k < |dif| ==> 0 <= dif[k] < n
    decreases |dif| - i
  {
    var s := dif[i];
    difmax := difmax[s := difmax[s] + 1];
    if difmax[s] > maxi { maxi := difmax[s]; }
    i := i + 1;
  }
  output := IntToString(maxi);
}
