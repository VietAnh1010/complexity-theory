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
    R := HeapPush(R, v);
    var tmp;
    R, tmp := HeapPop(R);
    s1 := s1 + v - tmp;
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
    B := HeapPush(B, -A[i]);
    var tmp;
    B, tmp := HeapPop(B);
    s2 := s2 + A[i] + tmp;
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

// heapq.heappush: append, then sift up
method HeapPush(h0: seq<int>, x: int) returns (h: seq<int>)
  ensures |h| == |h0| + 1
{
  h := h0 + [x];
  var i := |h| - 1;
  while i > 0
    invariant 0 <= i < |h|
    invariant |h| == |h0| + 1
    decreases i
  {
    var p := (i - 1) / 2;
    if h[i] < h[p] {
      var t := h[i];
      h := h[i := h[p]][p := t];
      i := p;
    } else {
      break;
    }
  }
}

// heapq.heappop: take the root, move the last item to the root, sift down
method HeapPop(h0: seq<int>) returns (h: seq<int>, top: int)
  requires |h0| > 0
  ensures |h| == |h0| - 1
{
  top := h0[0];
  var last := h0[|h0| - 1];
  h := h0[..|h0| - 1];
  if |h| > 0 {
    h := h[0 := last];
    var i := 0;
    while 2 * i + 1 < |h|
      invariant 0 <= i < |h|
      invariant |h| == |h0| - 1
      decreases |h| - i
    {
      var c := 2 * i + 1;
      if c + 1 < |h| && h[c + 1] < h[c] {
        c := c + 1;
      }
      if h[c] < h[i] {
        var t := h[i];
        h := h[i := h[c]][c := t];
        i := c;
      } else {
        break;
      }
    }
  }
}
