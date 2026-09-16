// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-23
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Both `SUM1` and `SUM2` computation loops rebuild `newR`/`newB` via a
//     full O(N) linear insertion scan on each of N outer iterations
//     (`while j < |R|`, invariant `|R| == N`), giving O(N**2), while
//     Python's real `heapq.heappush`/`heappop` are O(log N) each so the
//     Python is O(N log N) as labelled.
//
//   how this label could be wrong, and what to check:
//     The label O(nlogn) is right about the Python
//     (`heapq.heappush`/`heapq.heappop` are O(log N) each, N iterations,
//     O(N log N) total) but the Dafny replaces the heap with a linear-scan
//     insertion (`while j < |R|` / `while j < |B|`) rebuilt on every one
//     of N outer steps. Confirm the invariant `|R| == N` (resp. `|B| ==
//     N`) holds through the outer loop, so the inner scan is O(N) work
//     repeated N times, giving O(N**2) — check this is the same shape as
//     sibling `3029_114`.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 103, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "SumSeq"],
//     "loop_depth": 2, "loops": 5, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// p03714 AtCoder Beginner Contest 062 - 3N Numbers  (problem 3029, solution 3029_74)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import heapq
// 
// N=int(input())
// A=list(map(int,input().split()))
// 
// R=sorted(A[:N])
// SUM1=[sum(A[:N])]
// for i in range(N,2*N):
//     heapq.heappush(R,A[i])
//     tmp=heapq.heappop(R)
//     SUM1.append(SUM1[-1]+A[i]-tmp)
// 
// B=list(map(lambda x:x*(-1),A[2*N:3*N]))
// B.sort()
// SUM2=[-sum(B)]
// for i in range(2*N-1,N-1,-1):
//     heapq.heappush(B,-A[i])
//     tmp=heapq.heappop(B)
//     SUM2.append(SUM2[-1]+A[i]+tmp)
// 
// ans=-float("inf")
// for i in range(N+1):
//     ans=max(ans,SUM1[i]-SUM2[-(i+1)])
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, digits: seq<int>) returns (output: string)
  requires n >= 0
  requires |digits| == 3 * n
{
  var N := n;
  var A := digits;

  // SUM1[k] = max sum picking N of the first (N+k) elements, k = 0..N
  var R := SortInts(A[0..N]);
  var s1 := SumSeq(A[0..N]);
  var SUM1 := seq(N + 1, _ => 0);
  SUM1 := SUM1[0 := s1];
  var i := N;
  var idx1 := 1;
  while i < 2 * N
    invariant N <= i <= 2 * N
    invariant |R| == N
    invariant |SUM1| == N + 1
    invariant idx1 == i - N + 1
    decreases 2 * N - i
  {
    var v := A[i];
    var newR: seq<int> := [];
    var j := 0;
    var inserted := false;
    while j < |R|
      invariant 0 <= j <= |R|
      invariant |newR| == j + (if inserted then 1 else 0)
      decreases |R| - j
    {
      if !inserted && v <= R[j] {
        newR := newR + [v];
        inserted := true;
      }
      newR := newR + [R[j]];
      j := j + 1;
    }
    if !inserted {
      newR := newR + [v];
    }
    var tmp := newR[0];
    s1 := s1 + v - tmp;
    R := newR[1..];
    SUM1 := SUM1[idx1 := s1];
    idx1 := idx1 + 1;
    i := i + 1;
  }

  // SUM2[k] for k = 0..N (heap of negated suffix values, tracked in positive terms)
  var sub := A[2 * N..3 * N];
  var negSub := seq(|sub|, k requires 0 <= k < |sub| => -sub[k]);
  var B := SortInts(negSub);
  var s2 := -SumSeq(B);
  var SUM2 := seq(N + 1, _ => 0);
  SUM2 := SUM2[0 := s2];
  i := 2 * N - 1;
  var idx2 := 1;
  while i >= N
    invariant N - 1 <= i <= 2 * N - 1
    invariant |B| == N
    invariant |SUM2| == N + 1
    invariant idx2 == 2 * N - i
    decreases i - (N - 1)
  {
    var v := -A[i];
    var newB: seq<int> := [];
    var j := 0;
    var inserted := false;
    while j < |B|
      invariant 0 <= j <= |B|
      invariant |newB| == j + (if inserted then 1 else 0)
      decreases |B| - j
    {
      if !inserted && v <= B[j] {
        newB := newB + [v];
        inserted := true;
      }
      newB := newB + [B[j]];
      j := j + 1;
    }
    if !inserted {
      newB := newB + [v];
    }
    var tmp := newB[0];
    s2 := s2 + A[i] + tmp;
    B := newB[1..];
    SUM2 := SUM2[idx2 := s2];
    idx2 := idx2 + 1;
    i := i - 1;
  }

  var ans := SUM1[0] - SUM2[N];
  i := 1;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant |SUM1| == N + 1 && |SUM2| == N + 1
    decreases N + 1 - i
  {
    var cand := SUM1[i] - SUM2[N - i];
    if cand > ans {
      ans := cand;
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
