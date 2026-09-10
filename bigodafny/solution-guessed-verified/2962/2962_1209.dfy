// 2962_1209 (problem 2962) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : 20 * (|first_name| + |second_name|) * (|first_name| + |second_name|)
//   proved class    : O(n**2+m**2)
//   agent verdict   : proves
//   reference label : O(n**2+m**2)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     outer loop over |need| letters, each iteration does two full
//     O(|need|)/O(|total|) count scans -- classic quadratic count-based
//     anagram check.
//
//   agent notes:
//     Charged seq concat (need := first_name+second_name) at its real cost
//     |first_name|+|second_name|. Each outer iteration does two O(n) count
//     scans, so O(n) per iteration over n iterations gives n^2. Needed
//     MulAdd/MulMonoRight lemmas to isolate the multiplications (early
//     mismatch exit means i<n at loop exit, so needed monotonicity too).
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 2962_1209
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// first = input()
// second = input()
// total = input()
// need = first + second
// if len(need) != len(total):
// 	print("NO")
// else:
// 	for letters in need:
// 		if need.count(letters) != total.count(letters): 
// 			print("NO")
// 			exit()
// 	print("YES")
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulAdd(a: int, x: int, d: int)
  ensures a * (x + d) == a * x + a * d
{}

lemma MulMonoRight(a: int, p: int, q: int)
  requires a >= 0 && p <= q
  ensures a * p <= a * q
{}

lemma FinalBound(n: int, s: int, pre: int)
  requires n >= 0
  requires pre >= 0
  requires s <= (4 * n + 20) * n + 20
  ensures pre + s + 10 <= 20 * n * n + 20 * n + 20 * pre + 30
{}

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 20 * (|first_name| + |second_name|) * (|first_name| + |second_name|)
                  + 20 * (|first_name| + |second_name|) + 20 * |jumbled_name| + 30
{
  var need := first_name + second_name;
  ghost var pre: nat := |first_name| + |second_name|; // real cost of seq concat
  var total := jumbled_name;
  if |need| != |total| {
    output := "NO";
    steps := pre + 5;
  } else {
    var mismatch := false;
    var i := 0;
    ghost var s: nat := 0;
    while i < |need| && !mismatch
      invariant 0 <= i <= |need|
      invariant s <= (4 * |need| + 20) * i + 20
      decreases |need| - i
    {
      var ch := need[i];
      var cNeed := 0;
      var j := 0;
      ghost var sj: nat := 0;
      while j < |need|
        invariant 0 <= j <= |need|
        invariant sj <= 2 * j + 2
        decreases |need| - j
      {
        if need[j] == ch { cNeed := cNeed + 1; }
        j := j + 1;
        sj := sj + 2;
      }
      var cTotal := 0;
      var k := 0;
      ghost var sk: nat := 0;
      while k < |total|
        invariant 0 <= k <= |total|
        invariant sk <= 2 * k + 2
        decreases |total| - k
      {
        if total[k] == ch { cTotal := cTotal + 1; }
        k := k + 1;
        sk := sk + 2;
      }
      if cNeed != cTotal { mismatch := true; }
      assert sj <= 2 * |need| + 2;
      assert sk <= 2 * |total| + 2 == 2 * |need| + 2;
      s := s + sj + sk + 5;
      MulAdd(4 * |need| + 20, i, 1);
      i := i + 1;
    }
    MulMonoRight(4 * |need| + 20, i, |need|);
    assert s <= (4 * |need| + 20) * |need| + 20;
    if mismatch { output := "NO"; } else { output := "YES"; }
    FinalBound(|need|, s, pre);
    steps := pre + s + 10;
  }
}
