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

// Label O(nlogn+mlogm) -- the LABEL IS CORRECT and the TRANSLATION is wrong.
//
// This comment previously claimed the label named a sort the row does not
// contain. That was read off the Dafny alone. The Python sorts:
//
//     int_array_a = sorted(int_array_a)
//     int_array_b = sorted(int_array_b)
//     print(int_array_a[-1], int_array_b[-1])
//
// so it is genuinely O(n log n + m log m) and BigOBench measured it correctly.
// The Dafny below reaches the same answer with two linear `Max685` scans and is
// O(n+m). The bound proved here is sound -- it bounds this Dafny -- but the row
// is a defect under CLAUDE.md's "Translate the algorithm, not just the
// behaviour": replacing sort-then-take-last with a max scan changes the
// complexity class, and the label is what the dataset exists to carry.
//
// Sibling 685_777 is the instructive contrast. Its Python really does scan for
// a maximum without sorting, so its O(n+m) label is right. The two rows of
// problem 685 differ because THEIR PYTHONS DIFFER, which is the reason two
// solutions of one problem are kept. The inference that ran the other way --
// "the siblings compute the same answer, so one label must be wrong" -- is
// exactly backwards, and it is what produced the wrong conclusion here.
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
