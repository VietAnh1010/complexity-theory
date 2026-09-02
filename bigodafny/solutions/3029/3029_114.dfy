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

method Solve(n: int, digits: seq<int>) returns (output: string)
  requires n >= 0
  requires |digits| == 3 * n
{
  var N := n;
  var a := digits;

  // L[i] = max sum picking N of the first (N+i) elements, i = 0..N
  var heap := SortInts(a[0..N]);
  var s := SumSeq(heap);
  var L := seq(N + 1, _ => 0);
  L := L[0 := s];
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |heap| == N
    invariant |L| == N + 1
    decreases N - i
  {
    var v := a[N + i];
    var newHeap: seq<int> := [];
    var j := 0;
    var inserted := false;
    while j < |heap|
      invariant 0 <= j <= |heap|
      invariant |newHeap| == j + (if inserted then 1 else 0)
      decreases |heap| - j
    {
      if !inserted && v <= heap[j] {
        newHeap := newHeap + [v];
        inserted := true;
      }
      newHeap := newHeap + [heap[j]];
      j := j + 1;
    }
    if !inserted {
      newHeap := newHeap + [v];
    }
    var mn := newHeap[0];
    s := s + v - mn;
    heap := newHeap[1..];
    L := L[i + 1 := s];
    i := i + 1;
  }

  // R[k] = python's r[k] for k = 0..N (heap of negated values)
  var sub := a[2 * N..3 * N];
  var negSub := seq(|sub|, k requires 0 <= k < |sub| => -sub[k]);
  var heap2 := SortInts(negSub);
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
    var v := -a[idx];
    var newHeap: seq<int> := [];
    var j := 0;
    var inserted := false;
    while j < |heap2|
      invariant 0 <= j <= |heap2|
      invariant |newHeap| == j + (if inserted then 1 else 0)
      decreases |heap2| - j
    {
      if !inserted && v <= heap2[j] {
        newHeap := newHeap + [v];
        inserted := true;
      }
      newHeap := newHeap + [heap2[j]];
      j := j + 1;
    }
    if !inserted {
      newHeap := newHeap + [v];
    }
    var mn := newHeap[0];
    s2 := s2 + v - mn;
    heap2 := newHeap[1..];
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
