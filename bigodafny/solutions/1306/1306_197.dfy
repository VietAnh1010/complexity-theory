// 1011_B. Planning The Expedition  (problem 1306, solution 1306_197)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// 
// n,m = list(map(int,input().split()))
// l = list(map(int,input().split()))
// 
// l2 = [y for x,y in Counter(l).items()]
// l2.sort(reverse=True)
// 
// #print(l2)
// 
// for i in range(1,max(l2)+2):
// 	if sum(int(x/i) for x in l2) < n:
// 		print(i-1)
// 		break
// else:
// 	print()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountOccur1306c(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + CountOccur1306c(a[1..], v)
}

function RemoveAll1306c(a: seq<int>, v: int): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else if a[0] == v then RemoveAll1306c(a[1..], v)
  else [a[0]] + RemoveAll1306c(a[1..], v)
}

function GroupCounts1306c(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else [CountOccur1306c(a, a[0])] + GroupCounts1306c(RemoveAll1306c(a[1..], a[0]))
}

function SumDiv1306c(counts: seq<int>, day: int): int
  requires day > 0
  decreases |counts|
{
  if |counts| == 0 then 0
  else counts[0] / day + SumDiv1306c(counts[1..], day)
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var counts := GroupCounts1306c(a_list);
  var maxC := if |counts| > 0 then MaxSeq(counts) else 0;
  var i := 1;
  var found := false;
  var result := 0;
  while i <= maxC + 1 && !found
    decreases (if found then 0 else 1), maxC + 2 - i
  {
    if SumDiv1306c(counts, i) < n {
      result := i - 1;
      found := true;
    } else {
      i := i + 1;
    }
  }
  output := if found then IntToString(result) else "";
}
