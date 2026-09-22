// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n + sum of digit lengths of the printed values)
//   cause          : label
//   confidence     : high
//   auditor        : value-vs-size convention, 2026-09-22
//
//   The label disagrees with the code under the value-versus-size
//   convention. BigOBench fitted its labels by profiling, which treats a
//   capped input value as constant; COMPLEXITY.md section 1 decides the
//   opposite. This row is where the two disagree.
//
//   evidence:
//     Machine-checked. The proof in solutions-proved/276/276_610.dfy
//     verifies the bound
//
//       steps <= 13 * n + BoundFor(abc_list[..min(n, |abc_list|)]) + 2
//
//     The BoundFor term is IntToString's digit-length charge on the values
//     printed by the YES branch, so it grows with the MAGNITUDE of the
//     input numbers -- log of a value -- while the O(n) label was fitted
//     against the test-case count alone.
//
//     Same shape as 2381_156, moved here on 2026-09-17: "IntToString costs
//     the digit count, i.e. log of the value". Found by prove-sample-4.
//
// 1385_A. Three Pairwise Maximums  (problem 276, solution 276_610)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
// 	x, y, z = map(int, input().split())
// 	if(x != y and y != z and x!= z):
// 		print("NO")
// 	elif(x == y and x != z and x == min(x, z)):
// 		print("NO")
// 	elif(y == z and y != x and y == min(y, x)):
// 		print("NO")
// 	elif(x == z and x != y and x == min(y, z)):
// 		print("NO")
// 	else:
// 		print("YES")
// 		print(min({x, y, z}), min({x, y, z}), max({x, y, z}))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, abc_list: seq<seq<int>>) returns (output: string)
  requires forall r :: r in abc_list ==> |r| == 3
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |abc_list|
    invariant 0 <= i
    decreases n - i
  {
    var row := abc_list[i];
    var x := row[0];
    var y := row[1];
    var z := row[2];
    if x != y && y != z && x != z {
      parts := parts + ["NO\n"];
    } else if x == y && x != z && x == Min2(x, z) {
      parts := parts + ["NO\n"];
    } else if y == z && y != x && y == Min2(y, x) {
      parts := parts + ["NO\n"];
    } else if x == z && x != y && x == Min2(y, z) {
      parts := parts + ["NO\n"];
    } else {
      var mn := MinSeq(row);
      var mx := MaxSeq(row);
      parts := parts + ["YES\n" + IntToString(mn) + " " + IntToString(mn) + " " + IntToString(mx) + "\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}

function Min2(a: int, b: int): int { if a < b then a else b }
