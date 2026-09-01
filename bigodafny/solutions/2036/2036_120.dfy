// 471_A. MUH and Sticks  (problem 2036, solution 2036_120)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

method Solve(numbers: seq<int>) returns (output: string)
{
  var sticksL := numbers;
  var lNum := 0;
  var idx := 0;
  var stopped := false;
  while idx < |sticksL| && !stopped
    decreases |sticksL| - idx
  {
    var x := sticksL[idx];
    var cnt := 0;
    var j := 0;
    while j < |sticksL|
      decreases |sticksL| - j
    {
      if sticksL[j] == x { cnt := cnt + 1; }
      j := j + 1;
    }
    lNum := cnt;
    if lNum > 3 { stopped := true; }
    idx := idx + 1;
  }
  var distinctVals: seq<int> := [];
  idx := 0;
  while idx < |sticksL|
    decreases |sticksL| - idx
  {
    var x := sticksL[idx];
    if x !in distinctVals {
      distinctVals := distinctVals + [x];
    }
    idx := idx + 1;
  }
  var distinct := |distinctVals|;
  if lNum > 3 && (distinct == 3 || (distinct == 2 && lNum > 4)) {
    output := "Bear";
  } else if lNum > 3 {
    output := "Elephant";
  } else {
    output := "Alien";
  }
}
