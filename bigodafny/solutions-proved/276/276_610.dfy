// 1385_A. Three Pairwise Maximums  (problem 276, solution 276_610)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Re-proved tight 2026-09-22, after COMPLEXITY.md settled that IntToString(x)
// and |IntToString(x)| each cost 1.
//
//   The earlier proof charged Join by SumLen(parts), the REAL total length of
//   the printed strings, and carried a BoundFor term that grew with the
//   magnitude of the input numbers. That bound was sound but it made the row
//   look structural, which is why it was filed looser-structural and moved to
//   solutions-disputed/. Both moves have been withdrawn.
//
//   Under the settled charge every part has a charged length that does not
//   depend on any value: "NO\n" is a literal, and the YES piece is four
//   literals plus three IntToString results, each charged 1. So Join over k
//   parts costs a constant times k, and the bound is linear in n.
//
//   No digit-length lemma survives in this file, and that is deliberate. A
//   ghost function measuring |IntToString(x)| would put back exactly the term
//   the charge decision removed.
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

function Min2(a: int, b: int): int { if a < b then a else b }

// The charged length of one output part. Both branches are constants under
// COMPLEXITY.md's table: a string literal costs its own length, and each
// IntToString result is charged 1 however many digits it really has.
//
//   "NO\n"                                             ->  3
//   "YES\n" + s + " " + s + " " + s + "\n", s charged 1  ->  4 + 3 + 3 = 10
//
// so 10 covers either branch.
const PART_CHARGE: nat := 10

method Solve(n: int, abc_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall r :: r in abc_list ==> |r| == 3
  requires n >= 0
  ensures steps <= 24 * n + 2
{
  var parts: seq<string> := [];
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  while i < n && i < |abc_list|
    invariant 0 <= i <= n
    invariant i <= |abc_list|
    invariant |parts| == i
    invariant steps <= base1 + 12 * i
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
    steps := steps + 12;
  }
  output := Join(parts, "");
  // Join costs (charged length of the parts) + |parts|; each part is charged
  // PART_CHARGE, so this is (PART_CHARGE + 1) * |parts|, and |parts| == i <= n.
  steps := steps + (PART_CHARGE + 1) * |parts| + 1;
}
