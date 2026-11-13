// 768_A. Oath of the Night's Watch  (problem 1997, solution 1997_311)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// stewards = sorted(list(map(int, input().split())))
// help = 0
// mx = max(stewards)
// mn = min(stewards)
// 
// for each in stewards:
//     if mn < each < mx:
//         help += 1
// 
// print(help)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| > 0
  ensures steps <= 2 * NLogN(|a_list|) + 4 * |a_list| + 5 + |output|
{
  var stewards := SortInts(a_list);
  steps := SortCost(|a_list|);
  SortCostWithin(|a_list|, |a_list|);
  var mx := MaxSeq(stewards);
  var mn := MinSeq(stewards);
  steps := steps + 2 * |stewards|;
  ghost var base := steps;
  var help := 0;
  var i := 0;
  while i < |stewards|
    invariant 0 <= i <= |stewards|
    invariant |stewards| == |a_list|
    invariant steps == base + 4 * i
    decreases |stewards| - i
  {
    if mn < stewards[i] < mx {
      help := help + 1;
    }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(help);
  IntToStringDigits(help);
  steps := steps + Digits(help);
}
