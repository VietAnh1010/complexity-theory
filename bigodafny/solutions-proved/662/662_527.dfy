// 1342_B. Binary Period  (problem 662, solution 662_527)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # list( map(int, input().split()) )
// rw = int(input())
// for ewqr in range(rw):
//     t = input()
//     if t.count('1') == 0 or t.count('0') == 0:
//         print(t)
//         continue
//     s = '01' * len(t)
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

// CountChar and Repeat(t, |t|) each cost |t|; the honest per-row cost is the
// row's own length, not O(1), so the total is additive over the row lengths.
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

lemma SumLenPrefixLe(xs: seq<string>, k: nat)
  requires k <= |xs|
  ensures SumLen(xs[..k]) <= SumLen(xs)
  decreases |xs| - k
{
  if k == |xs| {
    assert xs[..k] == xs;
  } else {
    assert xs[..k] + [xs[k]] == xs[..k+1];
    SumLenSnoc(xs[..k], xs[k]);
    SumLenPrefixLe(xs, k + 1);
  }
}

method Solve(n: int, binary_strings: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 5 * SumLen(binary_strings) + 4 * (if n > 0 then n else 0) + 3
{
  steps := 1;
  var parts: seq<string> := [];
  var i := 0;
  ghost var base1 := steps;
  while i < n && i < |binary_strings|
    invariant 0 <= i
    invariant i <= |binary_strings|
    invariant i <= (if n > 0 then n else 0)
    invariant steps <= base1 + 5 * SumLen(binary_strings[..i]) + 4 * i
    decreases n - i
  {
    var t := binary_strings[i];
    var c1 := CountChar(t, '1');
    var c0 := CountChar(t, '0');
    steps := steps + 2 * |t|;
    if c1 == 0 || c0 == 0 {
      parts := parts + [t + "\n"];
    } else {
      parts := parts + [Repeat("01", |t|) + "\n"];
    }
    assert binary_strings[..i+1] == binary_strings[..i] + [binary_strings[i]];
    SumLenSnoc(binary_strings[..i], binary_strings[i]);
    i := i + 1;
    steps := steps + 3 * |t| + 4;
  }
  output := Join(parts, "");
  SumLenPrefixLe(binary_strings, i);
  steps := steps + 2;
}
