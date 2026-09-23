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

// Number of 1-entries in s[..k]: matches the count of taxi drivers seen so
// far. The problem guarantees m (== |taxis|, once the classify loop
// finishes) taxi drivers, and m >= 1.
function CountOnesUpTo(s: seq<int>, k: nat): nat
  requires k <= |s|
  decreases k
{
  if k == 0 then 0 else CountOnesUpTo(s, k - 1) + (if s[k - 1] == 1 then 1 else 0)
}

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |d_list| == |c_list|
  requires CountOnesUpTo(d_list, |d_list|) >= 1
  ensures steps <= 6 * |c_list| + (3 * |c_list| + 7) * |c_list| + |output| + 5
{
  var passengers: seq<int> := [];
  var taxis: seq<int> := [];
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  while i < |c_list|
    invariant 0 <= i <= |c_list|
    invariant |taxis| == CountOnesUpTo(d_list, i)
    invariant |passengers| <= i
    invariant |taxis| <= i
    invariant steps <= base1 + 3 * i
    decreases |c_list| - i
  {
    if d_list[i] == 0 {
      passengers := passengers + [c_list[i]];
    } else if d_list[i] == 1 {
      taxis := taxis + [c_list[i]];
    }
    i := i + 1;
    steps := steps + 3;
  }
  var passengersSorted := SortInts(passengers);
  var taxisSorted := SortInts(taxis);
  steps := steps + |passengers| + |taxis|;
  var answer: seq<int> := seq(|taxisSorted|, k => 0);
  var pIdx := 0;
  ghost var base2 := steps;
  // BinarySearch does at most 3 * |taxisSorted| + 5 steps under the
  // loose (not tight, O(|arr|) rather than O(log |arr|)) scaffold below.
  ghost var C := 3 * |taxisSorted| + 7;
  while pIdx < |passengersSorted|
    invariant 0 <= pIdx <= |passengersSorted|
    invariant |answer| == |taxisSorted|
    invariant steps <= base2 + C * pIdx
    decreases |passengersSorted| - pIdx
  {
    ghost var bsteps;
    var idx;
    bsteps, idx := BinarySearch(taxisSorted, passengersSorted[pIdx]);
    answer := answer[idx := answer[idx] + 1];
    assert bsteps + 2 <= C;
    steps := steps + bsteps + 2;
    assert steps <= base2 + C * pIdx + C;
    MulDistrib(pIdx, 1, pIdx + 1, C);
    assert pIdx * C + C == (pIdx + 1) * C;
    pIdx := pIdx + 1;
    assert steps <= base2 + C * pIdx;
  }
  assert |taxisSorted| <= |c_list|;
  assert |passengersSorted| <= |c_list|;
  MulMonoRight(3, |taxisSorted|, |c_list|);
  assert C <= 3 * |c_list| + 7;
  MulMonoRight(|passengersSorted|, C, 3 * |c_list| + 7);
  MulMonoRight(3 * |c_list| + 7, |passengersSorted|, |c_list|);
  assert C * |passengersSorted| <= (3 * |c_list| + 7) * |c_list|;
  output := JoinInts(answer, " ");
  steps := steps + |output| + 3;
}

method BinarySearch(arr: seq<int>, target: int) returns (ghost steps: nat, idx: int)
  requires |arr| >= 1
  ensures 0 <= idx < |arr|
  ensures steps <= 3 * |arr| + 5
{
  var lower := 0;
  var upper := |arr| - 1;
  steps := 1;
  if upper == lower {
    idx := 0;
    return;
  }
  ghost var base1 := steps;
  ghost var cnt := 0;
  while lower < upper
    invariant 0 <= lower <= upper < |arr|
    invariant cnt <= (|arr| - 1) - (upper - lower)
    invariant steps <= base1 + 3 * cnt
    decreases upper - lower
  {
    var x := lower + (upper - lower) / 2;
    var val := arr[x];
    if target == val {
      idx := x;
      steps := steps + 1;
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
        steps := steps + 2;
        return;
      }
      lower := x;
    } else {
      upper := x;
      if lower == upper {
        idx := lower;
        steps := steps + 2;
        return;
      }
    }
    cnt := cnt + 1;
    steps := steps + 3;
  }
  idx := lower;
}
