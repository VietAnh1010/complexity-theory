// --- Python ---------------------------------------------------------
// sticksL = input().split()
// for i in sticksL:
//     lNum = sticksL.count(i)
//     if (lNum > 3):
//         break
// sticksL = set(sticksL)
// if(lNum > 3 and (len(sticksL) == 3 or (len(sticksL) == 2 and lNum > 4))):
//     print("Bear")
// elif(lNum > 3):
//     print("Elephant")
// else:
//     print("Alien")
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 7 * |numbers| * |numbers| + 20 * |numbers| + 20
{
  steps := 0;
  ghost var n := |numbers|;
  ghost var K := 7 * n + 12;
  var sticksL := numbers;
  var lNum := 0;
  var idx := 0;
  var stopped := false;
  while idx < |sticksL| && !stopped
    invariant idx <= n && |sticksL| == n && steps <= idx * K
    decreases |sticksL| - idx
  {
    ghost var s0 := steps;
    StepMul(idx, K);
    steps := steps + (4 + if idx < |sticksL| then 1 else 0);
    steps := steps + 1;
    var x := sticksL[idx];
    var cnt := 0;
    var j := 0;
    while j < |sticksL|
      invariant j <= n && steps <= s0 + 6 + 7 * j
      decreases |sticksL| - j
    {
      steps := steps + 3;
      steps := steps + 2;
      if sticksL[j] == x {
        steps := steps + 1;
        cnt := cnt + 1;
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 2;
    lNum := cnt;
    steps := steps + 1;
    if lNum > 3 {
      stopped := true;
    }
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + (3 + if idx < |sticksL| then 1 else 0);
  MulMono(idx, n, K);
  ghost var s1 := steps;
  SqEq(n);
  var distinctVals: seq<int> := [];
  idx := 0;
  while idx < |sticksL|
    invariant idx <= n && |sticksL| == n && steps <= s1 + 8 * idx
    decreases |sticksL| - idx
  {
    steps := steps + 3;
    steps := steps + 1;
    var x := sticksL[idx];
    steps := steps + 1;
    if x !in distinctVals {
      steps := steps + (1 + |[x]|);
      distinctVals := distinctVals + [x];
    }
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  steps := steps + 1;
  var distinct := |distinctVals|;
  steps := steps + (2 + if lNum > 3 then 2 + if distinct == 3 then 0 else 2 + if distinct == 2 then 1 else 0 else 0);
  if lNum > 3 && (distinct == 3 || (distinct == 2 && lNum > 4)) {
    output := "Bear";
  } else if lNum > 3 {
    output := "Elephant";
  } else {
    output := "Alien";
  }
}

import opened Prelude

ghost lemma StepMul(i: nat, K: nat)
  ensures (i + 1) * K == i * K + K
{}

ghost lemma MulMono(i: nat, n: nat, K: nat)
  requires i <= n
  ensures i * K <= n * K
{}

ghost lemma SqEq(n: nat)
  ensures n * (7 * n + 12) == 7 * n * n + 12 * n
{}
