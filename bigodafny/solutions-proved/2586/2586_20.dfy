// 546_B. Soldier and Badges  (problem 2586, solution 2586_20)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l1=list(map(int,input().split()))
// l2=[0]*int(n*(n+1)/2)
// cost=0
// for i in range (n):
//     if(l2[l1[i]-1]==0):
//         l2[l1[i]-1]=1
//     elif(l2[l1[i]-1]==1):
//         while(l2[l1[i]-1]==1):
//             cost+=1
//             l1[i]+=1
//         l2[l1[i]-1]=1
// print(cost)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Number of cells equal to 1 in s[lo..hi].
ghost function Ones(s: seq<int>, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else (if s[lo] == 1 then 1 else 0) + Ones(s, lo + 1, hi)
}

lemma OnesAll(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
  requires forall k :: lo <= k < hi ==> s[k] == 1
  ensures Ones(s, lo, hi) == hi - lo
  decreases hi - lo
{
  if lo < hi { OnesAll(s, lo + 1, hi); }
}

lemma OnesNone(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
  requires forall k :: lo <= k < hi ==> s[k] == 0
  ensures Ones(s, lo, hi) == 0
  decreases hi - lo
{
  if lo < hi { OnesNone(s, lo + 1, hi); }
}

lemma OnesSplit(s: seq<int>, lo: int, mid: int, hi: int)
  requires 0 <= lo <= mid <= hi <= |s|
  ensures Ones(s, lo, hi) == Ones(s, lo, mid) + Ones(s, mid, hi)
  decreases mid - lo
{
  if lo < mid { OnesSplit(s, lo + 1, mid, hi); }
}

lemma OnesUpdate(s: seq<int>, p: int, lo: int, hi: int)
  requires 0 <= p < |s|
  requires 0 <= lo <= hi <= |s|
  ensures Ones(s[p := 1], lo, hi) <= Ones(s, lo, hi) + 1
  decreases hi - lo
{
  if lo < hi { if lo == p { OnesUpdateOut(s, p, lo + 1, hi); } else { OnesUpdate(s, p, lo + 1, hi); } }
}

lemma OnesUpdateOut(s: seq<int>, p: int, lo: int, hi: int)
  requires 0 <= p < |s|
  requires 0 <= lo <= hi <= |s|
  ensures p < lo || hi <= p ==> Ones(s[p := 1], lo, hi) == Ones(s, lo, hi)
  decreases hi - lo
{
  if lo < hi { OnesUpdateOut(s, p, lo + 1, hi); }
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= 4 + n * (n + 1) / 2 + 16 * n + 7 * (n * (n - 1) / 2) + |output|
{
  steps := 0;
  steps := steps + 3;
  var size := n * (n + 1) / 2;
  steps := steps + size;
  var l2 := seq(size, _ /* _v0 */ => 0);
  OnesNone(l2, 0, size);
  var cost := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |l2| == size
    invariant Ones(l2, 0, size) <= i
    invariant 2 * cost <= i * (i - 1)
    invariant steps <= 3 + size + 16 * i + 7 * cost
    decreases n - i
  {
    ghost var s0 := steps;
    ghost var c0 := cost;
    steps := steps + 2;
    steps := steps + 2;
    var idx := a_list[i] - 1;
    steps := steps + 3;
    if 0 <= idx < size {
      steps := steps + 2;
      if l2[idx] == 0 {
        steps := steps + 1;
        OnesUpdate(l2, idx, 0, size);
        l2 := l2[idx := 1];
      } else {
        var j := idx;
        while j < size && l2[j] == 1
          invariant idx <= j <= size
          invariant |l2| == size
          invariant forall k :: idx <= k < j ==> l2[k] == 1
          invariant cost == c0 + (j - idx)
          invariant steps == s0 + 9 + 7 * (j - idx)
          decreases size - j
        {
          steps := steps + (3 + if j < size then 2 else 0);
          steps := steps + 1;
          cost := cost + 1;
          steps := steps + 1;
          j := j + 1;
        }
        OnesAll(l2, idx, j);
        OnesSplit(l2, 0, idx, size);
        OnesSplit(l2, idx, j, size);
        assert j - idx <= i;
        steps := steps + (2 + if j < size then 2 else 0);
        steps := steps + 1;
        if j < size {
          steps := steps + 1;
          OnesUpdate(l2, j, 0, size);
          l2 := l2[j := 1];
        }
      }
    }
    steps := steps + 1;
    i := i + 1;
    assert 2 * cost <= i * (i - 1) by {
      assert cost <= c0 + (i - 1);
      assert 2 * c0 <= (i - 1) * (i - 2);
      assert (i - 1) * (i - 2) + 2 * (i - 1) == i * (i - 1);
    }
  }
  steps := steps + 1;
  IntToStringDigits(cost);
  steps := steps + Digits(cost);
  output := IntToString(cost);
  assert 2 * cost <= n * (n - 1);
}
