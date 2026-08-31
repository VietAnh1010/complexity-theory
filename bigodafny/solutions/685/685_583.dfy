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
  output := ""; // TODO: translate the Python above
}
