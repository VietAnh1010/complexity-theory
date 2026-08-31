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

method Solve(n1: int, list1: seq<int>, n2: int, list2: seq<int>) returns (output: string)
{
  var max1 := Max685(list1);
  var max2 := Max685(list2);
  output := IntToString(max1) + " " + IntToString(max2);
}

method Max685(xs: seq<int>) returns (m: int)
  requires |xs| > 0
{
  m := xs[0];
  var i := 1;
  while i < |xs|
    decreases |xs| - i
  {
    if xs[i] > m { m := xs[i]; }
    i := i + 1;
  }
}
