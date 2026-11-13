// 1285_D. Dr. Evil Underscores  (problem 1870, solution 1870_81)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// n=int(input())
// arr=list(map(int,input().split()))
// def solve(arr,bit):
//     if len(arr)==0 or bit <0:
//         return 0
//     l=[]
//     r=[]
//     for i in arr:
//         if (i>>bit)&1==0:
//             l.append(i)
//         else:
//             r.append(i)
// 
// 
//     if len(l)==0:
//         return solve(r,bit-1)
// 
//     if len(r)==0:
//         return solve(l,bit-1)
// 
//     return min(solve(r,bit-1),solve(l,bit-1))+(1<<bit)
// print(solve(arr,30))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Pow2(bit: int): int
  requires bit >= 0
  ensures Pow2(bit) >= 1
  decreases bit
{
  if bit == 0 then 1 else 2 * Pow2(bit - 1)
}

function BitSet(x: int, bit: int): bool
  requires bit >= 0
{
  FloorMod(FloorDiv(x, Pow2(bit)), 2) == 1
}

function FilterOff(arr: seq<int>, bit: int): seq<int>
  requires bit >= 0
  decreases |arr|
{
  if |arr| == 0 then []
  else if !BitSet(arr[0], bit) then [arr[0]] + FilterOff(arr[1..], bit)
  else FilterOff(arr[1..], bit)
}

function FilterOn(arr: seq<int>, bit: int): seq<int>
  requires bit >= 0
  decreases |arr|
{
  if |arr| == 0 then []
  else if BitSet(arr[0], bit) then [arr[0]] + FilterOn(arr[1..], bit)
  else FilterOn(arr[1..], bit)
}

function MinXorSplit(arr: seq<int>, bit: int): int
  decreases bit
{
  if |arr| == 0 || bit < 0 then 0
  else
    var l := FilterOff(arr, bit);
    var r := FilterOn(arr, bit);
    if |l| == 0 then MinXorSplit(r, bit - 1)
    else if |r| == 0 then MinXorSplit(l, bit - 1)
    else
      var rr := MinXorSplit(r, bit - 1);
      var ll := MinXorSplit(l, bit - 1);
      (if rr < ll then rr else ll) + Pow2(bit)
}

lemma FilterLens1870(arr: seq<int>, bit: int)
  requires bit >= 0
  ensures |FilterOff(arr, bit)| + |FilterOn(arr, bit)| == |arr|
  decreases |arr|
{
  if |arr| > 0 { FilterLens1870(arr[1..], bit); }
}

ghost function XorCost1870(arr: seq<int>, bit: int): nat
  decreases bit + 1
{
  if |arr| == 0 || bit < 0 then 1
  else
    var l := FilterOff(arr, bit);
    var r := FilterOn(arr, bit);
    100 * |arr| + 100 +
    (if |l| == 0 then XorCost1870(r, bit - 1)
     else if |r| == 0 then XorCost1870(l, bit - 1)
     else XorCost1870(r, bit - 1) + XorCost1870(l, bit - 1))
}

lemma XorCostBound1870(arr: seq<int>, bit: int)
  requires bit >= -1
  ensures XorCost1870(arr, bit) <= 200 * ((bit + 1) * |arr|) + 200 * |arr| + 1
  decreases bit + 1
{
  if |arr| == 0 || bit < 0 {
  } else {
    var l := FilterOff(arr, bit);
    var r := FilterOn(arr, bit);
    FilterLens1870(arr, bit);
    XorCostBound1870(r, bit - 1);
    XorCostBound1870(l, bit - 1);
    CostMulDistrib(bit, 1, bit + 1, |arr|);
    CostMulDistrib(|l|, |r|, |arr|, bit);
    CostMulDistrib(bit, 1, bit + 1, |l|);
    CostMulDistrib(bit, 1, bit + 1, |r|);
  }
}

method Solve(n: int, values: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 6300 * |values| + 3 + |output|
{
  steps := 0;
  var best := MinXorSplit(values, 30);
  XorCostBound1870(values, 30);
  steps := steps + XorCost1870(values, 30);
  IntToStringDigits(best);
  steps := steps + Digits(best);
  output := IntToString(best);
}
