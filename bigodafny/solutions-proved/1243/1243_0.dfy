// 186_A. Comparing Strings  (problem 1243, solution 1243_0)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// g1=list(input())
// g2=list(input())
// cntr=0
// if sorted(g1)!=sorted(g2):
//     print('NO')
// else:
//     for i in range(len(g1)):
//         if g1[i]!=g2[i]:
//                 cntr=cntr+1
//     if cntr==2:
//         print('YES')
//     else:
//         print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
//
// Two sorts, one per input line, so the bound carries two independent
// recursion-tree terms and the label's `nlogn+mlogm` shape is visible in the
// postcondition rather than collapsed into one parameter.
//
// Prelude.Sort is a plain recursive merge sort and lives in prelude.dfy, which
// a proof may not instrument, so its cost is charged through SortCost, whose
// recursion mirrors Sort's own split. SortCostNLogN proves the tight bound by
// a recursion-tree argument over a CEILING log: both halves of a split of size
// k are at most ceil(k/2), and CeilLog2(ceil(k/2)) == CeilLog2(k) - 1 holds by
// definition. With a floor log the inductive step is false at k = 3.
//
// The sequence comparison `a != b` is charged |s1| + |s2|, elementwise, the
// same charge the table gives `multiset(a) == multiset(b)`.

// The equality test sorts, as the Python does. An earlier translation compared
// multisets instead: same answer on every test, one complexity class cheaper,
// and the O(nlogn+mlogm) label then described nothing in this file.
method Solve(s1: string, s2: string) returns (output: string, ghost steps: nat)
  // One line on purpose: proofs.py's bound_of reads a single line, so a
  // wrapped `ensures` is recorded truncated in data/complexity_proofs.jsonl.
  ensures steps <= 2 * |s1| * (CeilLog2(|s1|) + 1) + 2 * |s2| * (CeilLog2(|s2|) + 1) + 3 * |s1| + |s2| + 5
{
  SortCostTreeBound(|s1|);
  SortCostTreeBound(|s2|);

  var a := Sort(s1, (x: char, y: char) => x < y);
  var b := Sort(s2, (x: char, y: char) => x < y);
  steps := 1 + SortCost(|s1|) + SortCost(|s2|);

  // one elementwise comparison of the two sorted lines
  steps := steps + |s1| + |s2| + 1;

  if a != b {
    output := "NO";
  } else {
    assert |s1| == |a| == |b| == |s2|;
    ghost var base := steps;
    var cntr := 0;
    var i := 0;
    while i < |s1|
      invariant 0 <= i <= |s1|
      invariant steps == base + 2 * i
      decreases |s1| - i
    {
      if s1[i] != s2[i] { cntr := cntr + 1; }
      i := i + 1;
      steps := steps + 2;
    }
    output := if cntr == 2 then "YES" else "NO";
  }
  steps := steps + 1;
}
