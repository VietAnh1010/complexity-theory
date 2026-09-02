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

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>) returns (output: string)
{
  var need := first_name + second_name;
  var total := jumbled_name;
  if |need| != |total| {
    output := "NO";
  } else {
    var mismatch := false;
    var i := 0;
    while i < |need| && !mismatch
      invariant 0 <= i <= |need|
      decreases |need| - i
    {
      var ch := need[i];
      var cNeed := 0;
      var j := 0;
      while j < |need|
        invariant 0 <= j <= |need|
        decreases |need| - j
      {
        if need[j] == ch { cNeed := cNeed + 1; }
        j := j + 1;
      }
      var cTotal := 0;
      var k := 0;
      while k < |total|
        invariant 0 <= k <= |total|
        decreases |total| - k
      {
        if total[k] == ch { cTotal := cTotal + 1; }
        k := k + 1;
      }
      if cNeed != cTotal { mismatch := true; }
      i := i + 1;
    }
    if mismatch { output := "NO"; } else { output := "YES"; }
  }
}
