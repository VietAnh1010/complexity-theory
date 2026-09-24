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

include "../../../../prelude.dfy"
import opened Prelude

// Sum of |a_list[k]| over the whole prefix. This is a VALUE, not a size: it
// is not bounded by |a_list| itself, since each v_k can be arbitrarily large.
ghost function SumAbsPrefix(s: seq<int>, t: nat): nat
  requires t <= |s|
  decreases t
{
  if t == 0 then 0 else SumAbsPrefix(s, t - 1) + AbsInt(s[t - 1])
}

// The length total Join actually charges (SumLen(parts) in the charge
// table's notation). Defined locally so its append behaviour is a one-line
// unfolding, not an induction.
ghost function SumLen1043(parts: seq<string>): nat
  decreases |parts|
{
  if |parts| == 0 then 0 else SumLen1043(parts[..|parts| - 1]) + |parts[|parts| - 1]|
}

lemma SumLen1043Append(parts: seq<string>, x: string)
  ensures SumLen1043(parts + [x]) == SumLen1043(parts) + |x|
{
  assert (parts + [x])[..|parts + [x]| - 1] == parts;
  assert (parts + [x])[|parts + [x]| - 1] == x;
}

lemma RepeatLen(s: string, n: nat)
  ensures |Repeat(s, n)| == n * |s|
  decreases n
{
  if n > 0 { RepeatLen(s, n - 1); }
}

// Each row prints "2" followed by (v-1) copies of "3": the output for that
// row has length v, and building it is charged O(v) -- Repeat("3", v-1)'s
// own cost, stipulated linear in its count (as CPython's `"3" * (v-1)` is a
// single O(v) operation), plus the O(v-1) concatenation joining "2" to it.
// v is the row's VALUE, not part of |a_list|'s size, so this is a real
// value-bounded cost the O(n) label -- counting only the number of rows --
// does not include.
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |a_list| + 3 * SumAbsPrefix(a_list, |a_list|) + 10
{
  var lines: seq<string> := [];
  var i := 0;
  ghost var totalLen: nat := 0;
  steps := 1;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant |lines| == i
    invariant totalLen == SumLen1043(lines)
    invariant totalLen <= 2 * i + SumAbsPrefix(a_list, i)
    invariant steps <= 1 + 5 * i + 2 * SumAbsPrefix(a_list, i)
    decreases |a_list| - i
  {
    var v := a_list[i];
    var oldLines := lines;
    var piece: string;
    if v == 1 {
      piece := "-1";
      steps := steps + 3;
    } else if v >= 2 {
      RepeatLen("3", v - 1);
      piece := "2" + Repeat("3", v - 1);
      steps := steps + 2 * (v - 1) + 5;
    } else {
      piece := "2";
      steps := steps + 3;
    }
    lines := oldLines + [piece];
    SumLen1043Append(oldLines, piece);
    totalLen := totalLen + |piece|;
    i := i + 1;
  }
  output := Join(lines, "\n");
  steps := steps + (totalLen + |lines|) + 1;
}
