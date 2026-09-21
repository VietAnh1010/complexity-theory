// 1150_C. Prefix Sum Primes  (problem 3034, solution 3034_1)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
//
// input = sys.stdin.readline
//
// n = int(input())
// a = list(map(int, input().split()))
//
// count = {1: 0, 2: 0}
//
// for i in a:
//     count[i] += 1
//
// if count[1] >= 1 and count[2] >= 1:
//     ans = [2] + [1] + [2]*(count[2]-1) + [1]*(count[1] - 1)
// elif count[1] == 0:
//     ans = [2] * count[2]
// elif count[2] == 0:
//     ans = [1] * count[1]
//
// print(' '.join([str(x) for x in ans]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function SumLenInts(xs: seq<int>): nat
  decreases |xs|
{
  if |xs| == 0 then 0 else |IntToString(xs[0])| + SumLenInts(xs[1..])
}

lemma SumLenIntsSingleDigit(xs: seq<int>)
  requires forall k :: 0 <= k < |xs| ==> 1 <= xs[k] <= 9
  ensures SumLenInts(xs) <= |xs|
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    IntToStringLen(xs[0]);
    SumLenIntsSingleDigit(xs[1..]);
  }
}

lemma SumLenIntsSnoc(xs: seq<int>, extra: int)
  ensures SumLenInts(xs + [extra]) == SumLenInts(xs) + |IntToString(extra)|
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    assert (xs + [extra])[1..] == xs[1..] + [extra];
    SumLenIntsSnoc(xs[1..], extra);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |a_list| + 6
{
  var c1 := 0;
  var c2 := 0;
  var i := 0;
  steps := 1;
  ghost var base0 := steps;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant c1 + c2 <= i
    invariant steps <= base0 + 3 * i
    decreases |a_list| - i
  {
    if a_list[i] == 1 {
      c1 := c1 + 1;
    } else if a_list[i] == 2 {
      c2 := c2 + 1;
    }
    i := i + 1;
    steps := steps + 3;
  }
  assert c1 + c2 <= |a_list|;
  var ans: seq<int> := [];
  ghost var base1 := steps;
  if c1 >= 1 && c2 >= 1 {
    ans := [2, 1];
    steps := steps + 1;
    var k := 0;
    ghost var b2 := steps;
    while k < c2 - 1
      invariant 0 <= k <= c2 - 1
      invariant |ans| == 2 + k
      invariant forall t :: t in ans ==> t == 1 || t == 2
      invariant steps <= b2 + 2 * k
      decreases (c2 - 1) - k
    {
      ans := ans + [2];
      k := k + 1;
      steps := steps + 2;
    }
    k := 0;
    ghost var b3 := steps;
    while k < c1 - 1
      invariant 0 <= k <= c1 - 1
      invariant |ans| == 2 + (c2 - 1) + k
      invariant forall t :: t in ans ==> t == 1 || t == 2
      invariant steps <= b3 + 2 * k
      decreases (c1 - 1) - k
    {
      ans := ans + [1];
      k := k + 1;
      steps := steps + 2;
    }
    assert |ans| == c1 + c2;
  } else if c1 == 0 {
    var k := 0;
    ghost var b2 := steps;
    while k < c2
      invariant 0 <= k <= c2
      invariant |ans| == k
      invariant forall t :: t in ans ==> t == 1 || t == 2
      invariant steps <= b2 + 2 * k
      decreases c2 - k
    {
      ans := ans + [2];
      k := k + 1;
      steps := steps + 2;
    }
    assert |ans| == c2;
  } else if c2 == 0 {
    var k := 0;
    ghost var b2 := steps;
    while k < c1
      invariant 0 <= k <= c1
      invariant |ans| == k
      invariant forall t :: t in ans ==> t == 1 || t == 2
      invariant steps <= b2 + 2 * k
      decreases c1 - k
    {
      ans := ans + [1];
      k := k + 1;
      steps := steps + 2;
    }
    assert |ans| == c1;
  }
  assert |ans| <= |a_list|;
  assert forall k :: 0 <= k < |ans| ==> 1 <= ans[k] <= 9 by {
    forall k | 0 <= k < |ans| ensures 1 <= ans[k] <= 9 {
      assert ans[k] in ans;
    }
  }
  SumLenIntsSingleDigit(ans);
  output := JoinInts(ans, " ");
  steps := steps + SumLenInts(ans) + |ans| + 2;
}
