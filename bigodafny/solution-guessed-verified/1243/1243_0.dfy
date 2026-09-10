// 1243_0 (problem 1243) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n)
//   proved bound    : 10 * |s1| + 10 * |s2| + 30
//   proved class    : O(n+m)
//   agent verdict   : proves
//   reference label : O(nlogn+mlogm)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     task.dfy checks multiset(s1)!=multiset(s2) (not solution.py's sorted()
//     sort) plus one linear scan; multiset build+compare charged at its
//     natural O(n) cost, no nested loop anywhere.
//
//   agent notes:
//     task.dfy uses multiset(s1)!=multiset(s2), not solution.py's
//     sorted()-based check -- a real translation difference. Charged
//     multiset build/compare at O(|s1|+|s2|) (a single pass / hash compare),
//     not assumed O(1) and not treated as an O(n) per-insert trap either. No
//     nonlinear lemmas needed; the single loop invariant was linear and Z3
//     closed it directly.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1243_0
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
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
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string, ghost steps: nat)
  ensures steps <= 10 * |s1| + 10 * |s2| + 30
{
  // multiset(s) builds a counter from the string and != compares two
  // counters -- both real O(|s|) operations (single pass / hash compare),
  // charged flatly here rather than assumed O(1).
  ghost var mcost: nat := |s1| + |s2| + 5;
  if multiset(s1) != multiset(s2) {
    output := "NO";
    steps := mcost + 5;
  } else {
    assert |s1| == |s2| by {
      assert |multiset(s1)| == |multiset(s2)|;
    }
    var cntr := 0;
    var i := 0;
    ghost var s: nat := 0;
    while i < |s1|
      invariant 0 <= i <= |s1|
      invariant s <= 3 * i + 3
      decreases |s1| - i
    {
      if s1[i] != s2[i] { cntr := cntr + 1; }
      i := i + 1;
      s := s + 3;
    }
    output := if cntr == 2 then "YES" else "NO";
    steps := mcost + s + 5;
  }
}
