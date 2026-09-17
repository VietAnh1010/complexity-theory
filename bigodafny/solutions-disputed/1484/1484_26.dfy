// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n * L)
//   cause          : label
//   confidence     : high
//   auditor        : value-vs-size convention, 2026-09-17
//
//   The label disagrees with the code under the value-versus-size
//   convention. BigOBench fitted its labels by profiling, which treats a
//   capped input value as constant; COMPLEXITY.md section 1 decides the
//   opposite. This row is where the two disagree.
//
//   evidence:
//     The label treats a string comparison as unit cost. StringLess
//     against a running best compares character by character, so the
//     per-iteration cost carries the string length L. The proved bound
//     is 6*|numbers|*MaxLen(numbers) + 4*MaxLen(numbers) + 6.
//
//   how this label could be wrong, and what to check:
//     Confirm the loop compares whole strings rather than a precomputed
//     key. Note the sibling row of the same problem sorts first and does
//     not have this shape, which is why only this row is affected.
//
//   note: the translation is NOT at fault in any of these four rows. The
//   proof in solutions-proved/ is correct and stays there.
// --------------------------------------------------------------------

// 172_A. Phone Code  (problem 1484, solution 1484_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[];i=0
// for _ in range(int(input())):l.append(input())
// a=max(l);b=min(l)
// while a[i]==b[i]:i+=1
// print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<string>) returns (output: string)
  requires |numbers| == n
  requires n >= 1
{
  var best := numbers[0];
  var worst := numbers[0];
  var idx := 1;
  while idx < |numbers|
    decreases |numbers| - idx
  {
    if StringLess(best, numbers[idx]) { best := numbers[idx]; }
    if StringLess(numbers[idx], worst) { worst := numbers[idx]; }
    idx := idx + 1;
  }
  var i := 0;
  while i < |best| && i < |worst| && best[i] == worst[i]
    decreases |best| - i
  {
    i := i + 1;
  }
  output := IntToString(i);
}
