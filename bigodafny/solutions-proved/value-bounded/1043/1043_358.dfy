// 1326_A. Bad Ugly Numbers  (problem 1043, solution 1043_358)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
//
// for _ in range(n):
//     v = int(input())
//     if v == 1:
//         print(-1)
//     else:
//         print("2" + "3" * (v - 1))
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

// Repeat("3", v - 1) costs v - 1, the MAGNITUDE of a_list[i], not the length of
// a_list. That value carries no bound tied to |a_list|, so the true cost is
// O(|a_list| + sum of the values), which is looser than the label's O(n) in
// the number of elements alone. Charged explicitly via SumPos, per the
// value-vs-size convention (COMPLEXITY.md).
ghost function Pos(v: int): nat { if v > 0 then v else 0 }

ghost function SumPos(s: seq<int>, upto: nat): nat
  requires upto <= |s|
  decreases upto
{
  if upto == 0 then 0 else SumPos(s, upto - 1) + Pos(s[upto - 1])
}

lemma SumPosSnoc(s: seq<int>, upto: nat)
  requires upto < |s|
  ensures SumPos(s, upto + 1) == SumPos(s, upto) + Pos(s[upto])
{
}

lemma RepeatLen(s: string, k: nat)
  ensures |Repeat(s, k)| == k * |s|
  decreases k
{
  if k == 0 {
  } else {
    RepeatLen(s, k - 1);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |a_list| + 2 * SumPos(a_list, |a_list|) + 3
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  ghost var lineLenSum: nat := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= 1 + 5 * i + SumPos(a_list, i)
    invariant lineLenSum <= 2 * i + SumPos(a_list, i)
    invariant |lines| == i
    decreases |a_list| - i
  {
    SumPosSnoc(a_list, i);
    var v := a_list[i];
    if v == 1 {
      lines := lines + ["-1"];
      lineLenSum := lineLenSum + 2;
      steps := steps + 2;
    } else if v >= 2 {
      RepeatLen("3", v - 1);
      lines := lines + ["2" + Repeat("3", v - 1)];
      lineLenSum := lineLenSum + 1 + (v - 1);
      steps := steps + 2 + (v - 1);
    } else {
      lines := lines + ["2"];
      lineLenSum := lineLenSum + 1;
      steps := steps + 2;
    }
    i := i + 1;
    steps := steps + 1;
  }
  output := Join(lines, "\n");
  steps := steps + lineLenSum + |lines| + 1;
}
