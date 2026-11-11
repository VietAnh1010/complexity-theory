// --- Python ---------------------------------------------------------
// n = int(input())
// a = input().split()
// b = set(a)
// maximum = -1
// maximum_id = []
// for i in b:
//     x = a.count(i)
//     if x > maximum:
//         maximum_id = [int(i)]
//         maximum = x
//     elif x == maximum:
//         maximum_id.append(int(i))
// a = a[::-1]
// maximum = -1
// answer = -1
// for i in maximum_id:
//     x = a.index(str(i))
//     if x > maximum:
//         answer = i
//         maximum = x
// print(answer)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 28 * (|a_list| * |a_list|) + 27 * |a_list| + 10 + |output|
{
  steps := 0;
  var maxCount := -1;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= i * (8 * |a_list| + 7)
    decreases |a_list| - i
  {
    steps := steps + 3;
    var cnt := 0;
    var j := 0;
    ghost var s0 := steps;
    while j < |a_list|
      invariant 0 <= j <= |a_list|
      invariant steps <= s0 + 8 * j
      decreases |a_list| - j
    {
      steps := steps + 3;
      steps := steps + 3;
      if a_list[j] == a_list[i] {
        steps := steps + 1;
        cnt := cnt + 1;
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    if cnt > maxCount {
      maxCount := cnt;
    }
    steps := steps + 1;
    MulStep(i, 8 * |a_list| + 7);
    i := i + 1;
  }
  steps := steps + 2;
  ghost var base := steps;
  var answer := -1;
  steps := steps + 1;
  var bestLast := |a_list|;
  var seen: seq<int> := [];
  var k := 0;
  while k < |a_list|
    invariant 0 <= k <= |a_list|
    invariant |seen| <= k
    invariant steps <= base + 1 + k * (20 * |a_list| + 20)
    decreases |a_list| - k
  {
    steps := steps + 3;
    steps := steps + 1;
    var v := a_list[k];
    var alreadySeen := false;
    var sp := 0;
    ghost var s1 := steps;
    while sp < |seen|
      invariant 0 <= sp <= |seen|
      invariant steps <= s1 + 6 * sp
      decreases |seen| - sp
    {
      steps := steps + 3;
      steps := steps + 2;
      if seen[sp] == v {
        alreadySeen := true;
      }
      steps := steps + 1;
      sp := sp + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    if !alreadySeen {
      steps := steps + (1 + |[v]|);
      seen := seen + [v];
      var cnt2 := 0;
      var p := 0;
      ghost var s2 := steps;
      while p < |a_list|
        invariant 0 <= p <= |a_list|
        invariant steps <= s2 + 7 * p
        decreases |a_list| - p
      {
        steps := steps + 3;
        steps := steps + 2;
        if a_list[p] == v {
          steps := steps + 1;
          cnt2 := cnt2 + 1;
        }
        steps := steps + 1;
        p := p + 1;
      }
      steps := steps + 2;
      steps := steps + 1;
      if cnt2 == maxCount {
        var lastIdx := -1;
        var q := 0;
        ghost var s3 := steps;
        while q < |a_list|
          invariant 0 <= q <= |a_list|
          invariant steps <= s3 + 6 * q
          decreases |a_list| - q
        {
          steps := steps + 3;
          steps := steps + 2;
          if a_list[q] == v {
            lastIdx := q;
          }
          steps := steps + 1;
          q := q + 1;
        }
        steps := steps + 2;
        steps := steps + 1;
        if lastIdx < bestLast {
          bestLast := lastIdx;
          answer := v;
        }
      }
    }
    steps := steps + 1;
    MulStep(k, 20 * |a_list| + 20);
    k := k + 1;
  }
  steps := steps + 2;
  steps := steps + Digits(answer);
  output := IntToString(answer);
  IntToStringDigits(answer);
  Final(|a_list|);
}

lemma MulStep(i: nat, K: nat)
  ensures (i + 1) * K == i * K + K
{
}

lemma Final(N: nat)
  ensures N * (8 * N + 7) + N * (20 * N + 20) + 5 <= 28 * (N * N) + 27 * N + 10
{
  assert N * (8 * N + 7) == 8 * (N * N) + 7 * N;
  assert N * (20 * N + 20) == 20 * (N * N) + 20 * N;
}

import opened Prelude
