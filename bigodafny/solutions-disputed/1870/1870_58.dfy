// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny calls `MinXorSplit(values, 30)`, which filters the values
//     into two lists per bit over a fixed 31 levels, O(n), with no sort;
//     the Python sorts first, O(n log n) as labelled, then splits sorted
//     ranges.
//
//   how this label could be wrong, and what to check:
//     The Python's first step is `sorted(...)`, and its stack search
//     depends on the sorted order to find each split point. Check that the
//     Dafny never sorts: `MinXorSplit` partitions with
//     `FilterOff`/`FilterOn` at each of 31 bit levels, O(n) per level,
//     which is the sibling 1870_81's algorithm, not this row's.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 49, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 5, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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

method Solve(n: int, values: seq<int>) returns (output: string)
{
  var best := MinXorSplit(values, 30);
  output := IntToString(best);
}
