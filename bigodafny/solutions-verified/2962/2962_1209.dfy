// 141_A. Amusing Joke  (problem 2962, solution 2962_1209)
// time complexity: O(n**2+m**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
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
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(n**2+m**2) -- agrees. This is the only row in the dataset carrying it.
// The outer loop runs over `need` (the two names concatenated, n+m tokens) and
// each iteration scans `need` and `total` in full, so the cost is
// |need|·(|need|+|total|). With |need| == |total| == n+m that is (n+m)^2, and
// (n+m)^2 = n^2 + 2nm + m^2 = Theta(n^2 + m^2): the label drops the cross term,
// which is asymptotically free. The bound below is stated in the sequence
// lengths, which is the honest form -- the two names' sizes are what vary.
// Z3 does not do nonlinear arithmetic. The outer loop's invariant multiplies
// the iteration count by a per-iteration cost, so that one step is isolated.
lemma MulStep(i: nat, c: nat)
  ensures (i + 1) * c == i * c + c
{ }

lemma MulMonoLeft(p: nat, q: nat, c: nat)
  requires p <= q
  ensures p * c <= q * c
{ }

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>)
  returns (output: string, ghost steps: nat)
  ensures steps <= (|first_name| + |second_name|) *
                   (2 * (|first_name| + |second_name|) + 2 * |jumbled_name| + 6)
                 + |first_name| + |second_name| + |jumbled_name| + 6
{
  var need := first_name + second_name;
  var total := jumbled_name;
  steps := |first_name| + |second_name| + |jumbled_name| + 3;
  if |need| != |total| {
    output := "NO";
    steps := steps + 2;
  } else {
    var mismatch := false;
    ghost var s0 := steps;
    var i := 0;
    while i < |need| && !mismatch
      invariant 0 <= i <= |need|
      invariant steps <= s0 + i * (2 * |need| + 2 * |total| + 6)
      decreases |need| - i
    {
      ghost var sIter := steps;
      var ch := need[i];
      var cNeed := 0;
      var j := 0;
      while j < |need|
        invariant 0 <= j <= |need|
        invariant steps == sIter + 2 * j
        decreases |need| - j
      {
        if need[j] == ch { cNeed := cNeed + 1; }
        j := j + 1;
        steps := steps + 2;
      }
      var cTotal := 0;
      var k := 0;
      while k < |total|
        invariant 0 <= k <= |total|
        invariant steps == sIter + 2 * |need| + 2 * k
        decreases |total| - k
      {
        if total[k] == ch { cTotal := cTotal + 1; }
        k := k + 1;
        steps := steps + 2;
      }
      if cNeed != cTotal { mismatch := true; }
      MulStep(i, 2 * |need| + 2 * |total| + 6);
      i := i + 1;
      steps := steps + 6;
    }
    MulMonoLeft(i, |need|, 2 * |need| + 2 * |total| + 6);
    assert |need| == |first_name| + |second_name|;
    if mismatch { output := "NO"; } else { output := "YES"; }
    steps := steps + 2;
  }
}
