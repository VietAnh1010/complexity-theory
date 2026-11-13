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

ghost function Log2(x: nat): nat  decreases x
{ if x <= 1 then 0 else 1 + Log2(x / 2) }

lemma Log2Mono(x: nat, y: nat)
  requires x <= y
  ensures Log2(x) <= Log2(y)
  decreases y
{
  if x >= 2 { Log2Mono(x / 2, y / 2); }
}

lemma Log2LeCeil(x: nat)
  ensures Log2(x) <= CeilLog2(x)
  decreases x
{
  if x > 1 {
    Log2LeCeil(x / 2);
    CeilLog2Monotone(x / 2, (x + 1) / 2);
  }
}

lemma Log2Dbl(x: nat)
  requires x >= 1
  ensures Log2(2 * x) == 1 + Log2(x)
  ensures Log2(2 * x + 1) == 1 + Log2(x)
{
  assert (2 * x) / 2 == x;
  assert (2 * x + 1) / 2 == x;
}

method Solve(n: int, digits: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |digits| == 3 * n
  ensures steps <= 44 * NLogN(3 * n + 1) + 130 * (3 * n + 1) + 120 + |output|
{
  var N := n;
  var A := digits;
  ghost var K := 22 * SearchPot(N + 1) + 60;
  steps := 1;

  var R := SortInts(A[0..N]);
  var s1 := SumSeq(A[0..N]);
  var SUM1 := seq(N + 1, _ => 0);
  SortCostWithin(N, 3 * N + 1);
  steps := steps + SortCost(N) + 2 * N + 10;
  SUM1 := SUM1[0 := s1];
  var i := N;
  var idx1 := 1;
  ghost var t: nat := 0;
  ghost var base1 := steps;
  while i < 2 * N
    invariant N <= i <= 2 * N
    invariant |R| == N
    invariant |SUM1| == N + 1
    invariant idx1 == i - N + 1
    invariant t == i - N
    invariant steps <= base1 + t * K
    decreases 2 * N - i
  {
    var v := A[i];
    ghost var sp: nat;
    ghost var sq: nat;
    R, sp := HeapPush(R, v);
    var tmp;
    R, tmp, sq := HeapPop(R);
    Log2Mono(N, N + 1);
    Log2LeCeil(N + 1);
    s1 := s1 + v - tmp;
    SUM1 := SUM1[idx1 := s1];
    idx1 := idx1 + 1;
    i := i + 1;
    steps := steps + 9 + sp + sq;
    CostMulDistrib(t, 1, t + 1, K);
    t := t + 1;
  }
  SearchLoopWithin(N, N + 1, 3 * N + 1, 22, 60);

  var sub := A[2 * N..3 * N];
  var negSub := seq(|sub|, k requires 0 <= k < |sub| => -sub[k]);
  var B := SortInts(negSub);
  var s2 := -SumSeq(B);
  var SUM2 := seq(N + 1, _ => 0);
  steps := steps + SortCost(N) + 3 * N + 10;
  SUM2 := SUM2[0 := s2];
  i := 2 * N - 1;
  var idx2 := 1;
  t := 0;
  base1 := steps;
  while i >= N
    invariant N - 1 <= i <= 2 * N - 1
    invariant |B| == N
    invariant |SUM2| == N + 1
    invariant idx2 == 2 * N - i
    invariant t == 2 * N - 1 - i
    invariant steps <= base1 + t * K
    decreases i - (N - 1)
  {
    ghost var sp: nat;
    ghost var sq: nat;
    B, sp := HeapPush(B, -A[i]);
    var tmp;
    B, tmp, sq := HeapPop(B);
    Log2Mono(N, N + 1);
    Log2LeCeil(N + 1);
    s2 := s2 + A[i] + tmp;
    SUM2 := SUM2[idx2 := s2];
    idx2 := idx2 + 1;
    i := i - 1;
    steps := steps + 9 + sp + sq;
    CostMulDistrib(t, 1, t + 1, K);
    t := t + 1;
  }
  SearchLoopWithin(N, N + 1, 3 * N + 1, 22, 60);
  SortCostWithin(N, 3 * N + 1);

  var ans := SUM1[0] - SUM2[N];
  i := 1;
  steps := steps + 4;
  base1 := steps;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant |SUM1| == N + 1 && |SUM2| == N + 1
    invariant steps <= base1 + 8 * i
    decreases N + 1 - i
  {
    var cand := SUM1[i] - SUM2[N - i];
    if cand > ans {
      ans := cand;
    }
    i := i + 1;
    steps := steps + 8;
  }
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + Digits(ans);
}

method HeapPush(h0: seq<int>, x: int) returns (h: seq<int>, ghost steps: nat)
  ensures |h| == |h0| + 1
  ensures steps <= 10 * Log2(|h0| + 1) + 13
{
  h := h0 + [x];
  steps := 3;
  var i := |h| - 1;
  ghost var it: nat := 0;
  while i > 0
    invariant 0 <= i < |h|
    invariant |h| == |h0| + 1
    invariant it + Log2(i + 1) <= Log2(|h0| + 1)
    invariant steps == 3 + 10 * it
    decreases i
  {
    var p := (i - 1) / 2;
    steps := steps + 10;
    if h[i] < h[p] {
      var t := h[i];
      h := h[i := h[p]][p := t];
      assert p + 1 == (i + 1) / 2;
      i := p;
      it := it + 1;
    } else {
      break;
    }
  }
}

method HeapPop(h0: seq<int>) returns (h: seq<int>, top: int, ghost steps: nat)
  requires |h0| > 0
  ensures |h| == |h0| - 1
  ensures steps <= 12 * Log2(|h0|) + 18
{
  top := h0[0];
  var last := h0[|h0| - 1];
  h := h0[..|h0| - 1];
  steps := 6;
  if |h| > 0 {
    h := h[0 := last];
    var i := 0;
    ghost var it: nat := 0;
    while 2 * i + 1 < |h|
      invariant 0 <= i < |h|
      invariant |h| == |h0| - 1
      invariant it <= Log2(i + 1)
      invariant steps == 6 + 12 * it
      decreases |h| - i
    {
      var c := 2 * i + 1;
      steps := steps + 12;
      if c + 1 < |h| && h[c + 1] < h[c] {
        c := c + 1;
      }
      if h[c] < h[i] {
        var t := h[i];
        h := h[i := h[c]][c := t];
        Log2Dbl(i + 1);
        i := c;
        it := it + 1;
      } else {
        Log2Mono(i + 1, |h|);
        Log2Mono(|h|, |h0|);
        break;
      }
    }
    Log2Mono(i + 1, |h|);
    Log2Mono(|h|, |h0|);
  }
}
