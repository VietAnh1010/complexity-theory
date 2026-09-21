// 59_B. Fortune Telling  (problem 384, solution 384_34)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// f = int(input())
// petals = list(map(int,input().split()))
// #print(f'suma: {sum(petals)}')
// while True:
//     if sum(petals)%2 == 1:
//         print(sum(petals))
//         break
//     else:
//         try:
//             m = min(i for i in petals if i%2)
//         except:
//             m = min(petals)
//         #print(f'removed: {m} ')
//         petals.remove(m)
//         #print(sum(petals))
//         #print(petals)
//     if petals == []:
//         print(0)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function SumSeq(xs: seq<int>): int
  decreases |xs|
{
  if |xs| == 0 then 0 else xs[0] + SumSeq(xs[1..])
}

function RemoveFirst(xs: seq<int>, v: int): seq<int>
  ensures v in xs ==> |RemoveFirst(xs, v)| == |xs| - 1
  ensures !(v in xs) ==> RemoveFirst(xs, v) == xs
  decreases |xs|
{
  if |xs| == 0 then []
  else if xs[0] == v then xs[1..]
  else [xs[0]] + RemoveFirst(xs[1..], v)
}

lemma QuadInductive(n: nat)
  requires n >= 1
  ensures 2 + 8 * n + (9 * (n - 1) * (n - 1) + 12 * (n - 1) + 8) <= 9 * n * n + 12 * n + 8
{
  var k := n - 1;
  assert n == k + 1;
  calc {
    2 + 8 * n + (9 * k * k + 12 * k + 8);
    ==
    2 + 8 * (k + 1) + 9 * k * k + 12 * k + 8;
    ==
    9 * k * k + 20 * k + 18;
  }
  calc {
    9 * n * n + 12 * n + 8;
    ==
    9 * (k + 1) * (k + 1) + 12 * (k + 1) + 8;
    ==
    9 * k * k + 18 * k + 9 + 12 * k + 12 + 8;
    ==
    9 * k * k + 30 * k + 29;
  }
  assert 2 + 8 * n + (9 * (n - 1) * (n - 1) + 12 * (n - 1) + 8) == 9 * k * k + 20 * k + 18;
  assert 9 * n * n + 12 * n + 8 == 9 * k * k + 30 * k + 29;
}

// Each call does O(|petals|) local work (SumSeq, two linear scans,
// RemoveFirst -- each a recursive seq function, charged its length) and
// recurses once on a strictly shorter seq. Sum_{k=0}^{n} O(k) = O(n**2).
method Reduce(petals: seq<int>) returns (result: string, ghost steps: nat)
  decreases |petals|
  ensures steps <= 9 * |petals| * |petals| + 12 * |petals| + 8
{
  steps := 1;
  if |petals| == 0 {
    result := "0";
    steps := steps + 1;
    return;
  }
  var s := SumSeq(petals);
  steps := steps + |petals|;
  if s % 2 == 1 {
    result := IntToString(s);
    steps := steps + 1;
    return;
  }
  var hasOdd := false;
  var mOdd := 0;
  var i := 0;
  while i < |petals|
    invariant 0 <= i <= |petals|
    invariant hasOdd ==> mOdd in petals
    invariant steps <= 2 + |petals| + 3 * i
    decreases |petals| - i
  {
    if petals[i] % 2 == 1 {
      if !hasOdd || petals[i] < mOdd {
        mOdd := petals[i];
        hasOdd := true;
      }
    }
    i := i + 1;
    steps := steps + 3;
  }
  var m: int;
  if hasOdd {
    m := mOdd;
    assert m in petals;
  } else {
    m := petals[0];
    var j := 1;
    while j < |petals|
      invariant 1 <= j <= |petals|
      invariant m in petals
      invariant steps <= 2 + |petals| + 3 * |petals| + 3 * j
      decreases |petals| - j
    {
      if petals[j] < m { m := petals[j]; }
      j := j + 1;
      steps := steps + 3;
    }
  }
  assert m in petals;
  assert steps <= 2 + 7 * |petals|;
  var newPetals := RemoveFirst(petals, m);
  steps := steps + |petals|;
  assert |newPetals| == |petals| - 1;
  assert steps <= 2 + 8 * |petals|;
  if |newPetals| == 0 {
    result := "0";
    steps := steps + 1;
  } else {
    ghost var recSteps: nat;
    result, recSteps := Reduce(newPetals);
    QuadInductive(|petals|);
    steps := steps + recSteps;
  }
}

method Solve(v_0: int, v_1: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 9 * |v_1| * |v_1| + 12 * |v_1| + 9
{
  output, steps := Reduce(v_1);
  steps := steps + 1;
}
