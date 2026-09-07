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
