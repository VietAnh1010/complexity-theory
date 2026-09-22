// LABEL AUDIT WITHDRAWN -- 2026-09-22.
//
//   This row was moved to solutions-disputed/ because its proof charged
//   IntToString by the digit count of the printed value, which made the cost
//   grow with the value's magnitude while the label counted only how many
//   items there were. That charge was the ENTIRE basis for the move.
//
//   COMPLEXITY.md now charges IntToString 1, and treats |IntToString(x)| as 1
//   as well so Join cannot reintroduce the digit count. Under that model this
//   row's label omits nothing, so the dispute does not exist and the row is
//   back in solutions/.
//
//   The proof in solutions-proved/ still carries the old digit term. That is
//   sound -- it charges MORE than the model requires, so it remains a valid
//   upper bound -- but it is now loose rather than structural, and it is
//   recorded as `looser-slack`. A tight re-proof is available work.
//
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
