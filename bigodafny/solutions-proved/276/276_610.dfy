// CHARGE SUPERSEDED -- 2026-09-22.
//
//   This proof charges IntToString by the digit count of the printed value.
//   COMPLEXITY.md now charges it 1, and |IntToString(x)| 1 as well. The proof
//   is still SOUND: charging more than the model requires leaves a valid upper
//   bound. It is simply loose, so the row's relation is `looser-slack`, not
//   `looser-structural`, and it left solutions-proved/value-bounded/.
//

include "../../prelude.dfy"
import opened Prelude

function Min2(a: int, b: int): int { if a < b then a else b }

// IntToString's output length is bounded loosely (linearly) by the value's
// magnitude -- far looser than the true O(log) growth, but enough to give
// Join's SumLen(parts) charge a finite closed form.
lemma IntToStringLenLoose(x: int)
  ensures |IntToString(x)| <= AbsInt(x) + 3
  decreases if x < 0 then 1 - x else x
{
  if x < 0 {
    IntToStringLenLoose(-x);
  } else if x < 10 {
  } else {
    IntToStringLenLoose(x / 10);
  }
}

lemma MinMax3AbsBound(x: int, y: int, z: int)
  ensures AbsInt(MinSeq([x, y, z])) <= AbsInt(x) + AbsInt(y) + AbsInt(z)
  ensures AbsInt(MaxSeq([x, y, z])) <= AbsInt(x) + AbsInt(y) + AbsInt(z)
{
  assert MinSeq([x, y, z]) == MinSeqFrom([x, y, z], 1, x);
  assert MinSeqFrom([x, y, z], 1, x) == MinSeqFrom([x, y, z], 2, if y < x then y else x);
  assert MinSeqFrom([x, y, z], 2, if y < x then y else x)
      == (if z < (if y < x then y else x) then z else (if y < x then y else x));
  assert MaxSeq([x, y, z]) == MaxSeqFrom([x, y, z], 1, x);
  assert MaxSeqFrom([x, y, z], 1, x) == MaxSeqFrom([x, y, z], 2, if y > x then y else x);
  assert MaxSeqFrom([x, y, z], 2, if y > x then y else x)
      == (if z > (if y > x then y else x) then z else (if y > x then y else x));
}

ghost function SumLen(xs: seq<string>): nat
{
  if |xs| == 0 then 0 else |xs[0]| + SumLen(xs[1..])
}

lemma SumLenSnoc(xs: seq<string>, extra: string)
  ensures SumLen(xs + [extra]) == SumLen(xs) + |extra|
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    assert (xs + [extra])[1..] == xs[1..] + [extra];
    SumLenSnoc(xs[1..], extra);
  }
}

ghost function BoundFor(rows: seq<seq<int>>): nat
  requires forall r :: r in rows ==> |r| == 3
  decreases |rows|
{
  if |rows| == 0 then 0
  else (3 * (AbsInt(rows[0][0]) + AbsInt(rows[0][1]) + AbsInt(rows[0][2])) + 20) + BoundFor(rows[1..])
}

lemma BoundForSnoc(rows: seq<seq<int>>, extra: seq<int>)
  requires forall r :: r in rows ==> |r| == 3
  requires |extra| == 3
  ensures BoundFor(rows + [extra]) == BoundFor(rows) + (3 * (AbsInt(extra[0]) + AbsInt(extra[1]) + AbsInt(extra[2])) + 20)
  decreases |rows|
{
  if |rows| == 0 {
  } else {
    assert (rows + [extra])[1..] == rows[1..] + [extra];
    BoundForSnoc(rows[1..], extra);
  }
}

method Solve(n: int, abc_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall r :: r in abc_list ==> |r| == 3
  requires n >= 0
  ensures steps <= 13 * n + BoundFor(abc_list[..(if n < |abc_list| then n else |abc_list|)]) + 2
{
  var parts: seq<string> := [];
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  while i < n && i < |abc_list|
    invariant 0 <= i <= n
    invariant i <= |abc_list|
    invariant |parts| == i
    invariant SumLen(parts) <= BoundFor(abc_list[..i])
    invariant steps <= base1 + 12 * i
    decreases n - i
  {
    var row := abc_list[i];
    var x := row[0];
    var y := row[1];
    var z := row[2];
    ghost var partsBefore := parts;
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
      assert row == [x, y, z];
      MinMax3AbsBound(x, y, z);
      IntToStringLenLoose(mn);
      IntToStringLenLoose(mx);
      var piece := "YES\n" + IntToString(mn) + " " + IntToString(mn) + " " + IntToString(mx) + "\n";
      assert |piece| == 7 + 2 * |IntToString(mn)| + |IntToString(mx)|;
      parts := parts + [piece];
    }
    assert |parts[|parts| - 1]| <= 3 * (AbsInt(x) + AbsInt(y) + AbsInt(z)) + 20;
    SumLenSnoc(partsBefore, parts[|parts| - 1]);
    assert parts == partsBefore + [parts[|parts| - 1]];
    BoundForSnoc(abc_list[..i], row);
    assert abc_list[..i] + [row] == abc_list[..i + 1];
    i := i + 1;
    steps := steps + 12;
  }
  assert i == (if n < |abc_list| then n else |abc_list|);
  output := Join(parts, "");
  steps := steps + SumLen(parts) + |parts| + 1;
}
