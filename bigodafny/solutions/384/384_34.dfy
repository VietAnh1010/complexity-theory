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

method Reduce(petals: seq<int>) returns (result: string)
  decreases |petals|
{
  if |petals| == 0 {
    result := "0";
    return;
  }
  var s := SumSeq(petals);
  if s % 2 == 1 {
    result := IntToString(s);
    return;
  }
  var hasOdd := false;
  var mOdd := 0;
  var i := 0;
  while i < |petals|
    invariant hasOdd ==> mOdd in petals
    decreases |petals| - i
  {
    if petals[i] % 2 == 1 {
      if !hasOdd || petals[i] < mOdd {
        mOdd := petals[i];
        hasOdd := true;
      }
    }
    i := i + 1;
  }
  var m: int;
  if hasOdd {
    m := mOdd;
    assert m in petals;
  } else {
    m := petals[0];
    var j := 1;
    while j < |petals|
      invariant m in petals
      decreases |petals| - j
    {
      if petals[j] < m { m := petals[j]; }
      j := j + 1;
    }
  }
  assert m in petals;
  var newPetals := RemoveFirst(petals, m);
  if |newPetals| == 0 {
    result := "0";
  } else {
    result := Reduce(newPetals);
  }
}

method Solve(v_0: int, v_1: seq<int>) returns (output: string)
{
  output := Reduce(v_1);
}
