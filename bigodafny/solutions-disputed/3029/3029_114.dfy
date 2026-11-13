// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(nlogn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny heapifies N values and then runs 2N rounds of `HeapPush`
//     and `HeapPop`, each sifting O(log N) levels, so the cost is O(N log
//     N); the Python's `heapq.heappush`/`heappop` loops are the same.
//
//   how this label could be wrong, and what to check:
//     The label is linear and names a second size, but there is one size,
//     N, and each of 2N steps does a `heappush` and `heappop` on a heap of
//     N items, O(log N) each. Check the two loops calling
//     `HeapPush`/`HeapPop` (the Python's `heapq` calls); the class is O(N
//     log N).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 134, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "SumSeq"],
//     "loop_depth": 1, "loops": 6, "recursive_helpers": 4,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p03714 AtCoder Beginner Contest 062 - 3N Numbers  (problem 3029, solution 3029_114)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import heapq
// N=int(input())
// a=list(map(int,input().split()))
// l=[None]*(N+1)
// r=[None]*(N+1)
// h=a[:N]
// s=sum(h)
// heapq.heapify(h)
// l[0]=s
// for i in range(N):
//     heapq.heappush(h,a[i+N])
//     s+=a[i+N]-heapq.heappop(h)
//     l[i+1]=s
// h=list(map(lambda x:-x,a[2*N:]))
// heapq.heapify(h)
// s=sum(h)
// r[-1]=s
// for i in range(N):
//     heapq.heappush(h,-a[-N-i-1])
//     s+=-a[-N-i-1]-heapq.heappop(h)
//     r[-i-2]=s
// a=l[0]+r[0]
// for i in range(1,N+1):
//     if a<l[i]+r[i]:
//         a=l[i]+r[i]
// print(a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Binary min-heap on a seq<int>, as Python's heapq.
method SiftDown(h: seq<int>, start: int) returns (r: seq<int>)
  requires 0 <= start < |h|
  ensures |r| == |h|
{
  r := h;
  var pos := start;
  while 2 * pos + 1 < |r|
    invariant |r| == |h|
    invariant 0 <= pos < |r|
    decreases |r| - pos
  {
    var c := 2 * pos + 1;
    if c + 1 < |r| && r[c + 1] < r[c] {
      c := c + 1;
    }
    if r[c] < r[pos] {
      var t := r[pos];
      r := r[pos := r[c]];
      r := r[c := t];
      pos := c;
    } else {
      break;
    }
  }
}

method Heapify(h: seq<int>) returns (r: seq<int>)
  ensures |r| == |h|
{
  r := h;
  var k := |r| / 2 - 1;
  while k >= 0
    invariant |r| == |h|
    invariant k < |r|
    decreases k + 1
  {
    r := SiftDown(r, k);
    k := k - 1;
  }
}

method HeapPush(h: seq<int>, v: int) returns (r: seq<int>)
  ensures |r| == |h| + 1
{
  r := h + [v];
  var pos := |r| - 1;
  while pos > 0
    invariant |r| == |h| + 1
    invariant 0 <= pos < |r|
    decreases pos
  {
    var parent := (pos - 1) / 2;
    if r[pos] < r[parent] {
      var t := r[pos];
      r := r[pos := r[parent]];
      r := r[parent := t];
      pos := parent;
    } else {
      break;
    }
  }
}

method HeapPop(h: seq<int>) returns (top: int, r: seq<int>)
  requires |h| > 0
  ensures |r| == |h| - 1
{
  top := h[0];
  var last := h[|h| - 1];
  r := h[..|h| - 1];
  if |r| > 0 {
    r := r[0 := last];
    r := SiftDown(r, 0);
  }
}

method Solve(n: int, digits: seq<int>) returns (output: string)
  requires n >= 0
  requires |digits| == 3 * n
{
  var N := n;
  var a := digits;

  // L[i] = python's l[i]
  var heap := a[0..N];
  var s := SumSeq(heap);
  heap := Heapify(heap);
  var L := seq(N + 1, _ => 0);
  L := L[0 := s];
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |heap| == N
    invariant |L| == N + 1
    decreases N - i
  {
    heap := HeapPush(heap, a[i + N]);
    var mn;
    mn, heap := HeapPop(heap);
    s := s + a[i + N] - mn;
    L := L[i + 1 := s];
    i := i + 1;
  }

  // R[k] = python's r[k] for k = 0..N (heap of negated values)
  var sub := a[2 * N..3 * N];
  var heap2 := seq(|sub|, k requires 0 <= k < |sub| => -sub[k]);
  heap2 := Heapify(heap2);
  var s2 := SumSeq(heap2);
  var R := seq(N + 1, _ => 0);
  R := R[N := s2];
  i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |heap2| == N
    invariant |R| == N + 1
    decreases N - i
  {
    var idx := 2 * N - i - 1;
    heap2 := HeapPush(heap2, -a[idx]);
    var mn;
    mn, heap2 := HeapPop(heap2);
    s2 := s2 + -a[idx] - mn;
    R := R[N - i - 1 := s2];
    i := i + 1;
  }

  var best := L[0] + R[0];
  i := 1;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant |L| == N + 1 && |R| == N + 1
    decreases N + 1 - i
  {
    if L[i] + R[i] > best {
      best := L[i] + R[i];
    }
    i := i + 1;
  }
  output := IntToString(best);
}
