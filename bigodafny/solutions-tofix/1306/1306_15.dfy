// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     GroupCounts1306b recurses once per distinct value in a_list via
//     CountOccur1306b and RemoveAll1306b, each O(|remaining|); distinct
//     values are bounded by the description's 1<=a_i<=100, capping
//     recursion depth at 100 so total cost is O(m), and the days loop is a
//     hardcoded range(1,101) contributing only O(1). Python's dict_count
//     construction has the identical O(distinct*m)=O(m) shape.
//
//   how this label could be wrong, and what to check:
//     The label assumes GroupCounts1306b's recursion is quadratic in the
//     number of packages m. Check the description's constraint
//     1<=a_i<=100: distinct food types are capped at 100 regardless of m,
//     so GroupCounts and Python's `for element in set(type_pack):
//     dict_count[element]=type_pack.count(element)` both do at most 100
//     O(m) passes, i.e. O(m). If a_i were unbounded this would be O(m**2);
//     it is not.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 42, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 4, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1011_B. Planning The Expedition  (problem 1306, solution 1306_15)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num_part, num_pack = [int(i) for i in input().split(' ')]
// type_pack = input().split(' ')
// dict_count = {}
// for element in set(type_pack):
//     dict_count[element] = type_pack.count(element)
// count = 0
// for days in range(1,101):
// 	survival = 0
// 	for element in dict_count:
// 		survival += dict_count[element] // days
// 	if survival >= num_part:
// 		count += 1
// 	else:
// 		break
// 
// 
// print(count)
//   	 	    		  		 				 		  	  	 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountOccur1306b(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + CountOccur1306b(a[1..], v)
}

function RemoveAll1306b(a: seq<int>, v: int): seq<int>
  ensures |RemoveAll1306b(a, v)| <= |a|
  decreases |a|
{
  if |a| == 0 then []
  else if a[0] == v then RemoveAll1306b(a[1..], v)
  else [a[0]] + RemoveAll1306b(a[1..], v)
}

function GroupCounts1306b(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else [CountOccur1306b(a, a[0])] + GroupCounts1306b(RemoveAll1306b(a[1..], a[0]))
}

function SumDiv1306b(counts: seq<int>, day: int): int
  requires day > 0
  decreases |counts|
{
  if |counts| == 0 then 0
  else counts[0] / day + SumDiv1306b(counts[1..], day)
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var counts := GroupCounts1306b(a_list);
  var count := 0;
  var days := 1;
  while days <= 100 && SumDiv1306b(counts, days) >= n
    decreases 101 - days
  {
    count := count + 1;
    days := days + 1;
  }
  output := IntToString(count);
}
