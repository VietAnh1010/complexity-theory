// Shared helpers for translated solutions.
//
// Everything here exists because a direct Python->Dafny transliteration would
// otherwise be silently wrong or would be rewritten per solution.

module Prelude {

  // ---- integer division ---------------------------------------------------
  // Dafny's `/` and `%` are Euclidean: the remainder is always non-negative.
  // Python's `//` and `%` floor: the remainder takes the sign of the divisor.
  // They coincide exactly when the divisor is positive, so a transliteration
  // that uses `/` is correct until the first negative divisor and wrong after.

  function FloorDiv(a: int, b: int): int
    requires b != 0
  {
    if b > 0 || a % b == 0 then a / b else a / b - 1
  }

  function FloorMod(a: int, b: int): int
    requires b != 0
  {
    a - b * FloorDiv(a, b)
  }

  // ---- formatting ---------------------------------------------------------

  function DigitChar(d: int): char
  {
    "0123456789"[if 0 <= d < 10 then d else 0]
  }

  function IntToString(x: int): string
    decreases if x < 0 then 1 - x else x
  {
    if x < 0 then "-" + IntToString(-x)
    else if x < 10 then [DigitChar(x)]
    else IntToString(x / 10) + [DigitChar(x % 10)]
  }

  function Join(parts: seq<string>, sep: string): string
    decreases |parts|
  {
    if |parts| == 0 then ""
    else if |parts| == 1 then parts[0]
    else parts[0] + sep + Join(parts[1..], sep)
  }

  function JoinInts(xs: seq<int>, sep: string): string
  {
    Join(seq(|xs|, i requires 0 <= i < |xs| => IntToString(xs[i])), sep)
  }

  // ---- parsing ------------------------------------------------------------

  predicate IsSpace(c: char)
  {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
  }

  function SplitWs(s: string): seq<string>
  {
    SplitWsFrom(s, 0, "", [])
  }

  function SplitWsFrom(s: string, i: nat, cur: string, acc: seq<string>): seq<string>
    decreases |s| - i
  {
    if i >= |s| then (if |cur| > 0 then acc + [cur] else acc)
    else if IsSpace(s[i]) then
      SplitWsFrom(s, i + 1, "", if |cur| > 0 then acc + [cur] else acc)
    else
      SplitWsFrom(s, i + 1, cur + [s[i]], acc)
  }

  // ---- sorting ------------------------------------------------------------
  // Merge sort, so an O(n log n) translation stays O(n log n).

  function Merge<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool): seq<T>
    decreases |a| + |b|
  {
    if |a| == 0 then b
    else if |b| == 0 then a
    else if less(b[0], a[0]) then [b[0]] + Merge(a, b[1..], less)
    else [a[0]] + Merge(a[1..], b, less)
  }

  function Sort<T>(s: seq<T>, less: (T, T) -> bool): seq<T>
    decreases |s|
  {
    if |s| <= 1 then s
    else Merge(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less)
  }

  function SortInts(s: seq<int>): seq<int>
  {
    Sort(s, (x, y) => x < y)
  }
}
