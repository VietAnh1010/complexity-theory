// 1011_B. Planning The Expedition  (problem 1306, solution 1306_126)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import*
// R=lambda:map(int,input().split())
// n,m=R()
// a=Counter(R()).values()
// i=1
// while sum(x//i for x in a)>=n:i+=1
// print(i-1)
//           
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountOccur1306(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + CountOccur1306(a[1..], v)
}

function RemoveAll1306(a: seq<int>, v: int): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else if a[0] == v then RemoveAll1306(a[1..], v)
  else [a[0]] + RemoveAll1306(a[1..], v)
}

function GroupCounts1306(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else [CountOccur1306(a, a[0])] + GroupCounts1306(RemoveAll1306(a[1..], a[0]))
}

function SumDiv1306(counts: seq<int>, day: int): int
  requires day > 0
  decreases |counts|
{
  if |counts| == 0 then 0
  else counts[0] / day + SumDiv1306(counts[1..], day)
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var counts := GroupCounts1306(a_list);
  var maxC := if |counts| > 0 then MaxSeq(counts) else 0;
  var day := 1;
  while day <= maxC + 1 && SumDiv1306(counts, day) >= n
    decreases maxC + 2 - day
  {
    day := day + 1;
  }
  output := IntToString(day - 1);
}
