// 914_A. Perfect Squares  (problem 2358, solution 2358_421)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// ar = list(map(int, input().split()))
//
// maxim = -10 ** 6
//
// for i in ar:
//     if (i < 0 or (int(i ** 0.5)) ** 2 != i) and i > maxim:
//         maxim = i
//
// print(maxim)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// IntSqrt2358b linear-searches r upward; its cost is O(v) in the VALUE v,
// not O(1) -- a second, value-shaped parameter the O(n)-over-|a_list| label
// does not see (same shape as the value-magnitude note in PROMPT.md).
lemma SqLowerBound(a: int)
  requires a >= 1
  ensures a <= a * a
{}

ghost function SumPos(s: seq<int>, upto: nat): nat
  requires upto <= |s|
{
  if upto == 0 then 0
  else SumPos(s, upto - 1) + (if s[upto - 1] > 0 then s[upto - 1] else 0)
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 + 10 * |a_list| + 2 * SumPos(a_list, |a_list|)
{
  steps := 1;
  var maxim := -1000000;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= 1 + 10 * i + 2 * SumPos(a_list, i)
    decreases |a_list| - i
  {
    var v := a_list[i];
    var notSquare := true;
    if v >= 0 {
      var r, rsteps := IntSqrt2358b(v);
      notSquare := r * r != v;
      steps := steps + rsteps + 1;
    }
    if (v < 0 || notSquare) && v > maxim {
      maxim := v;
    }
    assert SumPos(a_list, i + 1) == SumPos(a_list, i) + (if a_list[i] > 0 then a_list[i] else 0);
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(maxim);
  steps := steps + 1;
}

method IntSqrt2358b(x: int) returns (r: int, ghost steps: nat)
  ensures steps <= 2 * (if x > 0 then x else 0) + 5
{
  steps := 1;
  r := 0;
  var xPos := if x > 0 then x else 0;
  while (r + 1) * (r + 1) <= x
    invariant r >= 0
    invariant r <= xPos
    invariant steps <= 1 + 2 * r
    decreases x - r
  {
    SqLowerBound(r + 1);
    r := r + 1;
    steps := steps + 2;
  }
}
