// 637_A. Voting for Photos  (problem 2947, solution 2947_115)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

lemma MulSucc(k: nat, X: nat)
  ensures (k + 1) * X == k * X + X
{ }

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 13 * |a_list| * |a_list| + 26 * |a_list| + |output| + 15
{
  steps := 1;
  var maxCount := -1;
  var i := 0;
  ghost var base0 := steps;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= base0 + i * (3 * |a_list| + 6)
  {
    var cnt := 0;
    var j := 0;
    ghost var baseJ := steps;
    while j < |a_list|
      invariant 0 <= j <= |a_list|
      invariant steps <= baseJ + 3 * j
    {
      if a_list[j] == a_list[i] { cnt := cnt + 1; }
      j := j + 1;
      steps := steps + 3;
    }
    assert steps <= baseJ + 3 * |a_list|;
    if cnt > maxCount { maxCount := cnt; }
    MulSucc(i, 3 * |a_list| + 6);
    i := i + 1;
    steps := steps + 6;
  }
  assert steps <= base0 + |a_list| * (3 * |a_list| + 6);

  var answer := -1;
  var bestLast := |a_list|;
  var seen: seq<int> := [];
  var k := 0;
  ghost var base1 := steps;
  while k < |a_list|
    invariant 0 <= k <= |a_list|
    invariant |seen| <= k
    invariant steps <= base1 + k * (10 * |a_list| + 20)
  {
    var v := a_list[k];
    var alreadySeen := false;
    var sp := 0;
    ghost var baseSp := steps;
    while sp < |seen|
      invariant 0 <= sp <= |seen|
      invariant steps <= baseSp + 3 * sp
    {
      if seen[sp] == v { alreadySeen := true; }
      sp := sp + 1;
      steps := steps + 3;
    }
    assert steps <= baseSp + 3 * |seen| <= baseSp + 3 * |a_list|;
    if !alreadySeen {
      seen := seen + [v];
      var cnt2 := 0;
      var p := 0;
      ghost var baseP := steps;
      while p < |a_list|
        invariant 0 <= p <= |a_list|
        invariant steps <= baseP + 3 * p
      {
        if a_list[p] == v { cnt2 := cnt2 + 1; }
        p := p + 1;
        steps := steps + 3;
      }
      assert steps <= baseP + 3 * |a_list|;
      if cnt2 == maxCount {
        var lastIdx := -1;
        var q := 0;
        ghost var baseQ := steps;
        while q < |a_list|
          invariant 0 <= q <= |a_list|
          invariant steps <= baseQ + 3 * q
        {
          if a_list[q] == v { lastIdx := q; }
          q := q + 1;
          steps := steps + 3;
        }
        assert steps <= baseQ + 3 * |a_list|;
        if lastIdx < bestLast {
          bestLast := lastIdx;
          answer := v;
        }
      }
    }
    MulSucc(k, 10 * |a_list| + 20);
    k := k + 1;
    steps := steps + 10;
  }
  assert steps <= base1 + |a_list| * (10 * |a_list| + 20);

  output := IntToString(answer);
  steps := steps + |output| + 2;
}
