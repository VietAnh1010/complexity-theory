// 1285_D. Dr. Evil Underscores  (problem 1870, solution 1870_58)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// seq = sorted(list(map(int, input().split())))
// 
// #Left (inc), Right(exc), bit to check, value to add 
// queue = [(0,n,30,0)]
// best = 2 ** 30
// while queue:
//     l, r, b, v = queue.pop()
//     if b >= 0:
//         mask = 1 << b
//         
//         if not mask & seq[l] and mask & seq[r - 1]:
//             for i in range(l, r):
//                 if mask & seq[i]:
//                     queue.append((l,i,b - 1, v + mask))
//                     queue.append((i,r,b - 1, v + mask))
//                     break
//         else:
//             queue.append((l, r, b - 1, v))
//     else:
//         best = min(best, v)
//         
// print(best)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Pow2(bit: int): int
  requires bit >= 0
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

method Solve(n: int, values: seq<int>) returns (output: string)
{
  var best := MinXorSplit(values, 30);
  output := IntToString(best);
}
