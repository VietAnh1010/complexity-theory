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
