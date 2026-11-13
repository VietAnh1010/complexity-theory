// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny sorts the five-element `b_list` and then does five fixed
//     divide-and-mod steps per element of `a_list`, O(n); the Python's
//     `prizes.sort()` is the same constant-size sort.
//
//   how this label could be wrong, and what to check:
//     The label's log factor can only be `prizes.sort()`, which sorts
//     exactly five prize costs, a constant. Check the input format for
//     five prizes (the Dafny requires `|b_list| == 5`); the remaining work
//     is one pass over the bars, so the class is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 30, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 208_D. Prizes, Prizes, more Prizes  (problem 1092, solution 1092_11)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// sum,a,b,c,d,e=0,0,0,0,0,0
// numbers = [int(x) for x in input().split(' ')]
// prizes = [int(x) for x in input().split(' ')]
// prizes.sort()
// 
// for num in numbers:
//     sum+=num
//     if sum >= prizes[4]:
//         e+=int(sum/prizes[4])
//         sum = sum%prizes[4]
//     if sum >= prizes[3]:
//         d+=int(sum/prizes[3])
//         sum = sum%prizes[3]
//     if sum >= prizes[2]:
//         c+=int(sum/prizes[2])
//         sum = sum%prizes[2]
//     if sum >= prizes[1]:
//         b+=int(sum/prizes[1])
//         sum = sum%prizes[1]
//     if sum >= prizes[0]:
//         a+=int(sum/prizes[0])
//         sum = sum%prizes[0]
// print(f'{a} {b} {c} {d} {e}')
// print(sum)
//   		 	    		 	 	  	   					 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |b_list| == 5
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
  ensures steps <= 53 * |a_list| + 2 * |output| + 60
{
  var prizes := SortInts(b_list);
  SortIntsKeepsElems(b_list);
  assert forall x :: x in prizes ==> x >= 1;
  assert prizes[0] in prizes && prizes[1] in prizes && prizes[2] in prizes && prizes[3] in prizes && prizes[4] in prizes;
  assert SortCost(5) <= 20 by { reveal SortCost(); }
  steps := SortCost(5) + 1;
  var aC := 0;
  var bC := 0;
  var cC := 0;
  var dC := 0;
  var eC := 0;
  var s := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps <= 21 + 53 * idx
    decreases |a_list| - idx
  {
    ghost var st0 := steps;
    s := s + a_list[idx];
    steps := steps + 3;
    if s >= prizes[4] { eC := eC + FloorDiv(s, prizes[4]); s := FloorMod(s, prizes[4]); steps := steps + 8; }
    steps := steps + 2;
    if s >= prizes[3] { dC := dC + FloorDiv(s, prizes[3]); s := FloorMod(s, prizes[3]); steps := steps + 8; }
    steps := steps + 2;
    if s >= prizes[2] { cC := cC + FloorDiv(s, prizes[2]); s := FloorMod(s, prizes[2]); steps := steps + 8; }
    steps := steps + 2;
    if s >= prizes[1] { bC := bC + FloorDiv(s, prizes[1]); s := FloorMod(s, prizes[1]); steps := steps + 8; }
    steps := steps + 2;
    if s >= prizes[0] { aC := aC + FloorDiv(s, prizes[0]); s := FloorMod(s, prizes[0]); steps := steps + 8; }
    steps := steps + 2;
    idx := idx + 1;
    assert steps <= st0 + 53;
  }
  var parts := [IntToString(aC), IntToString(bC), IntToString(cC), IntToString(dC), IntToString(eC)];
  var t := IntToString(s);
  output := Join(parts, " ") + "\n" + t;
  IntToStringDigits(aC); IntToStringDigits(bC); IntToStringDigits(cC); IntToStringDigits(dC); IntToStringDigits(eC);
  IntToStringDigits(s);
  JoinLen(parts, " ");
  assert parts[1..][1..][1..][1..][1..] == [] && parts[1..][1..][1..][1..] == [parts[4]] && parts[1..][1..][1..] == [parts[3], parts[4]];
  assert SumLen(parts) == Digits(aC) + Digits(bC) + Digits(cC) + Digits(dC) + Digits(eC);
  steps := steps + (SumLen(parts) + 5) + SumLen(parts) + |t| + 1;
}
