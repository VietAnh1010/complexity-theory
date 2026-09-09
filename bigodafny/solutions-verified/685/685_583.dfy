// 1206_A. Choose Two Numbers  (problem 685, solution 685_583)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num_n = int(input())
// input_a = input()
// array_a = input_a.split(" ")
// num_m = int(input())
// input_b = input()
// array_b = input_b.split(" ")
// int_array_a = []
// for i in array_a:
// 	int_array_a.append(int(i))
// int_array_b = []
// for i in array_b:
// 	int_array_b.append(int(i))
// int_array_a = sorted(int_array_a)
// int_array_b = sorted(int_array_b)
// print(int_array_a[-1], int_array_b[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(nlogn+mlogm) -- WRONG, and the label names a sort this row does not
// contain. Both `Max685` calls are single linear scans; nothing is ordered,
// compared pairwise, or partitioned. Honest bound O(n+m).
//
// This is the first label disproved for a log-bearing class. The failure is the
// O(n*m) failure in a new place: the label names structure the code does not
// have -- there a dimension that does not vary, here a sort that is absent.
// Sibling 685_777 carries O(n+m) for the same computation via MaxSeq, so the
// two rows of this problem disagree with each other and 685_777 is the right one.
method Solve(n1: int, list1: seq<int>, n2: int, list2: seq<int>)
  returns (output: string, ghost steps: nat)
  requires |list1| > 0 && |list2| > 0
  ensures steps <= 3 * |list1| + 3 * |list2| + 8
{
  var max1, s1 := Max685(list1);
  var max2, s2 := Max685(list2);
  output := IntToString(max1) + " " + IntToString(max2);
  steps := s1 + s2 + 4;
}

method Max685(xs: seq<int>) returns (m: int, ghost steps: nat)
  requires |xs| > 0
  ensures steps <= 3 * |xs| + 2
{
  steps := 2;
  m := xs[0];
  var i := 1;
  while i < |xs|
    invariant 1 <= i <= |xs|
    invariant steps == 3 * i - 1
    decreases |xs| - i
  {
    if xs[i] > m { m := xs[i]; }
    i := i + 1;
    steps := steps + 3;
  }
}
