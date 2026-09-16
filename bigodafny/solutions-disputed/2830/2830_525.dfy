// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-21
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve's outer `while len > 0` (n iterations) contains `while j < len
//     - 1 { idxArr[j] := idxArr[j+1]; ... }`, shifting ~len/2 array
//     entries every step; this faithfully mirrors Python's
//     `index_letras.pop((len-1)//2)` and `letras.pop(...)`, both O(n)
//     mid-list pops repeated n times, so both are O(n**2), not O(nlogn).
//
//   how this label could be wrong, and what to check:
//     The label assumes the O(n log n) `ans.sort()` dominates, but check
//     the `while len > 0` loop: each iteration pops the middle index and
//     shifts everything after it, an inner `while j < len - 1` loop of
//     size ~len/2, run once per len from n down to 1. If that shift is
//     present at every step, the total is Theta(n**2), which the sort's n
//     log n cannot beat.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 48, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 2, "loops": 4,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 746_B. Decoding  (problem 2830, solution 2830_525)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// letras = list(map(str, input()))
// letras_copy = letras.copy()
// index_letras = [i for i in range(n)]
// 
// decoding = []
// 
// while len(letras) != 0:
// 	decoding.append(index_letras[(len(letras)-1)//2])
// 	index_letras.pop((len(letras)-1)//2)
// 	letras.pop((len(letras)-1)//2)
// 
// ans = [(i, l) for i, l in zip(decoding, letras_copy)]
// ans.sort(key=(lambda i: i[0]))
// 
// saida = [l for i, l in ans]
// print(''.join(saida))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var sz := if n > 0 then n else 0;
  var idxArr := new int[sz];
  var i := 0;
  while i < sz
    invariant 0 <= i <= sz
  {
    idxArr[i] := i;
    i := i + 1;
  }
  var decoding := new int[sz];
  var len := sz;
  var step := 0;
  while len > 0
    invariant 0 <= len <= sz
    invariant 0 <= step <= sz
    invariant step + len == sz
    decreases len
  {
    var pos := (len - 1) / 2;
    decoding[step] := idxArr[pos];
    var j := pos;
    while j < len - 1
      invariant pos <= j <= len - 1
      decreases len - 1 - j
    {
      idxArr[j] := idxArr[j + 1];
      j := j + 1;
    }
    len := len - 1;
    step := step + 1;
  }
  var buf := new char[sz];
  var k := 0;
  while k < sz
    invariant 0 <= k <= sz
  {
    var target := decoding[k];
    if 0 <= target < sz && k < |s| {
      buf[target] := s[k];
    }
    k := k + 1;
  }
  output := buf[0..sz];
}
