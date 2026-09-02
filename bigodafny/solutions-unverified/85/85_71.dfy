// 1075_B. Taxi drivers and Lyft  (problem 85, solution 85_71)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def binary_search(array, target):
//     lower = 0
//     upper = len(array) - 1
//     if upper == lower:
//         return 0
//     while lower < upper:   # use < instead of <=
//         x = lower + (upper - lower) // 2
//         val = array[x]
//         if target == val:
//             return x
//         elif target > val:
//             if lower == x:   # these two are the actual lines
//                 dist_left = target - array[lower]
//                 dist_right = array[upper] - target
//                 if dist_left == dist_right or dist_left < dist_right:
//                     return lower
//                 elif dist_left > dist_right:
//                     return upper
//             lower = x
//         elif target < val:
//             upper = x
//             if lower == upper:
//                 return lower
// 
// 
// R = input()
// 
// x = list(map(int, input().split()))
// t = list(map(int, input().split()))
// 
// passengers = []
// taxis = []
// 
// for idx, val in enumerate(t):
//     if val == 0:
//         passengers.append(x[idx])
//     elif val == 1:
//         taxis.append(x[idx])
// 
// passengers.sort()
// taxis.sort()
// answer = [0] * len(taxis)
// 
// for i in passengers:
//     index = binary_search(taxis, i)
//     answer[index] += 1
// 
// ##
// print (' '.join(str(x) for x in answer ))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
{
  var passengers: seq<int> := [];
  var taxis: seq<int> := [];
  var i := 0;
  while i < |c_list|
    decreases |c_list| - i
  {
    if d_list[i] == 0 {
      passengers := passengers + [c_list[i]];
    } else if d_list[i] == 1 {
      taxis := taxis + [c_list[i]];
    }
    i := i + 1;
  }
  var passengersSorted := SortInts(passengers);
  var taxisSorted := SortInts(taxis);
  assume {:axiom} |taxisSorted| >= 1;
  var answer: seq<int> := seq(|taxisSorted|, k => 0);
  var pIdx := 0;
  while pIdx < |passengersSorted|
    decreases |passengersSorted| - pIdx
  {
    var idx := BinarySearch(taxisSorted, passengersSorted[pIdx]);
    assume {:axiom} 0 <= idx < |answer|;
    answer := answer[idx := answer[idx] + 1];
    pIdx := pIdx + 1;
  }
  output := JoinInts(answer, " ");
}

method BinarySearch(arr: seq<int>, target: int) returns (idx: int)
  requires |arr| >= 1
{
  var lower := 0;
  var upper := |arr| - 1;
  if upper == lower {
    idx := 0;
    return;
  }
  while lower < upper
    invariant 0 <= lower <= upper < |arr|
    decreases upper - lower
  {
    var x := lower + (upper - lower) / 2;
    var val := arr[x];
    if target == val {
      idx := x;
      return;
    } else if target > val {
      if lower == x {
        var distLeft := target - arr[lower];
        var distRight := arr[upper] - target;
        if distLeft == distRight || distLeft < distRight {
          idx := lower;
        } else {
          idx := upper;
        }
        return;
      }
      lower := x;
    } else {
      upper := x;
      if lower == upper {
        idx := lower;
        return;
      }
    }
  }
  idx := lower;
}
