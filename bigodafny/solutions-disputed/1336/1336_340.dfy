// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-08
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The final while loop performs `A := A[i := C[|C|-1]]` or `A := A[i
//     := C[|C|-2]]`, each an O(N) seq-update on the length-N sequence A,
//     and this can execute for up to N indices where A[i]==-1, giving
//     O(N**2) total; Python's `A[i]=...` list assignment is O(1), so
//     Python is genuinely O(n log n) via C.sort while the Dafny is
//     quadratic.
//
//   how this label could be wrong, and what to check:
//     The label assumes C.sort(key=...) costs O(n log n) as in Python. The
//     Dafny replaces that sort with an O(n) stable partition into
//     firstGroup/secondGroup (cheaper, not the issue). Instead check the
//     final while loop over i: `A := A[i := C[|C|-1]]` is a seq update on
//     A (length N) executed on an iteration where A[i]==-1, which can
//     happen for up to N indices, each update costing O(N); confirm this
//     by checking whether A is declared seq<int> rather than array<int>.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 76, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1283_C. Friends and Gifts  (problem 1336, solution 1336_340)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// A = list(map(int, input().split()))
// # n = 7
// # A = [0, 0, 1]
// A = [i-1 for i in A]
// B = [-1] * n
// for i in range(n):
// 	if A[i] != -1:
// 		B[A[i]] = i
// C = [i for i in range(n) if B[i] == -1]
// C.sort(key=lambda x: A[x] == B[x])
// for i in range(n):
// 	if A[i] == -1:
// 		if i != C[-1]:
// 			A[i] = C[-1]
// 			C.pop()
// 		else:
// 			A[i] = C[-2]
// 			C.pop(-2)
// print(' '.join([str(i+1) for i in A]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, tree_heights: seq<int>) returns (output: string)
  requires N == |tree_heights|
{
  var A := seq(N, i requires 0 <= i < N => tree_heights[i] - 1);
  var B := seq(N, i requires 0 <= i < N => -1);
  var idx := 0;
  while idx < N
    invariant 0 <= idx <= N
    invariant |B| == N
    decreases N - idx
  {
    if 0 <= A[idx] < N {
      B := B[A[idx] := idx];
    }
    idx := idx + 1;
  }
  var C: seq<int> := [];
  var t := 0;
  while t < N
    invariant 0 <= t <= N
    invariant forall k :: 0 <= k < |C| ==> 0 <= C[k] < N
    decreases N - t
  {
    if B[t] == -1 {
      C := C + [t];
    }
    t := t + 1;
  }
  var firstGroup: seq<int> := [];
  var secondGroup: seq<int> := [];
  var u := 0;
  while u < |C|
    invariant 0 <= u <= |C|
    invariant |A| == N
    invariant forall k :: 0 <= k < |C| ==> 0 <= C[k] < N
    invariant forall k :: 0 <= k < |firstGroup| ==> 0 <= firstGroup[k] < N
    invariant forall k :: 0 <= k < |secondGroup| ==> 0 <= secondGroup[k] < N
    decreases |C| - u
  {
    var x := C[u];
    assert x in C;
    if A[x] != -1 {
      firstGroup := firstGroup + [x];
    } else {
      secondGroup := secondGroup + [x];
    }
    u := u + 1;
  }
  C := firstGroup + secondGroup;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |A| == N
    invariant forall k :: 0 <= k < |C| ==> 0 <= C[k] < N
    decreases N - i
  {
    if A[i] == -1 {
      if |C| > 0 && i != C[|C| - 1] {
        A := A[i := C[|C| - 1]];
        C := C[..|C| - 1];
        assert forall k :: 0 <= k < |C| ==> 0 <= C[k] < N;
      } else if |C| >= 2 {
        A := A[i := C[|C| - 2]];
        var newC := C[..|C| - 2] + [C[|C| - 1]];
        assert forall k :: 0 <= k < |newC| ==> 0 <= newC[k] < N;
        C := newC;
      }
    }
    i := i + 1;
  }
  assert |A| == N;
  var outVals := seq(N, kk requires 0 <= kk < N => A[kk] + 1);
  output := JoinInts(outVals, " ") + "\n";
}
