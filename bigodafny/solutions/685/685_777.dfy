// 1206_A. Choose Two Numbers  (problem 685, solution 685_777)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// elementsOfA = [int(i) for i in input().split()]
// m = int(input())
// elementsOfB = [int(i) for i in input().split()]
// 
// largestElementOfA = -1
// largestElementOfB = -1
// 
// for item in elementsOfA:
//     if item > largestElementOfA:
//         largestElementOfA = item
// 
// for item in elementsOfB:
//     if item > largestElementOfB:
//         largestElementOfB = item
// 
// print (largestElementOfA, largestElementOfB)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n1: int, list1: seq<int>, n2: int, list2: seq<int>) returns (output: string)
{
  var maxA := if |list1| == 0 then -1 else MaxSeq(list1);
  var maxB := if |list2| == 0 then -1 else MaxSeq(list2);
  output := IntToString(maxA) + " " + IntToString(maxB);
}
