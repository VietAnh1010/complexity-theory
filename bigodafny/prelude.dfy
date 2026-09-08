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

  // ---- bracket sequences --------------------------------------------------
  // Two rows pop a stack on every ')'. That is safe exactly because the input
  // is a regular bracket sequence, which is a fact about every prefix.

  ghost function Opens(s: string, t: nat): nat
    requires t <= |s|
    decreases t
  {
    if t == 0 then 0 else Opens(s, t - 1) + (if s[t - 1] == '(' then 1 else 0)
  }

  ghost function Closes(s: string, t: nat): nat
    requires t <= |s|
    decreases t
  {
    if t == 0 then 0 else Closes(s, t - 1) + (if s[t - 1] == ')' then 1 else 0)
  }

  ghost predicate OnlyBrackets(s: string)
  {
    forall t :: 0 <= t < |s| ==> s[t] == '(' || s[t] == ')'
  }

  // every character is one or the other, so the two counts partition the prefix
  lemma OpensPlusCloses(s: string, t: nat)
    requires t <= |s|
    requires OnlyBrackets(s)
    ensures Opens(s, t) + Closes(s, t) == t
    decreases t
  {
    if t > 0 { OpensPlusCloses(s, t - 1); }
  }

  // ---- formatting ---------------------------------------------------------

  function DigitChar(d: int): char
  {
    "0123456789"[if 0 <= d < 10 then d else 0]
  }

  // Python subscripts from the end when the index is negative; Dafny faults.
  // Three rows read a negative index on real stored inputs, so a translation
  // that ignores this is WRONG there, not merely unproven.
  function PyIndex(i: int, len: int): int
    requires -len <= i < len
    ensures 0 <= PyIndex(i, len) < len
  {
    if i < 0 then len + i else i
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

  lemma IntToStringNonEmpty(x: int)
    ensures |IntToString(x)| >= 1
    decreases if x < 0 then 1 - x else x
  {
    if x < 0 { IntToStringNonEmpty(-x); }
    else if x >= 10 { IntToStringNonEmpty(x / 10); }
  }

  // Join can only be shorter than its parts if a part is empty.
  lemma JoinLenGeCount(parts: seq<string>, sep: string)
    requires forall k :: 0 <= k < |parts| ==> |parts[k]| >= 1
    ensures |Join(parts, sep)| >= |parts|
    decreases |parts|
  {
    if |parts| > 1 { JoinLenGeCount(parts[1..], sep); }
  }

  // With an empty separator Join distributes over concatenation, so a long
  // Join can be measured one uniform band at a time.
  lemma JoinSplitEmptySep(a: seq<string>, b: seq<string>)
    ensures Join(a + b, "") == Join(a, "") + Join(b, "")
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b;
    } else if |a| == 1 {
      if |b| == 0 {
        assert a + b == a;
      } else {
        assert (a + b)[1..] == b;
      }
    } else {
      assert (a + b)[1..] == a[1..] + b;
      JoinSplitEmptySep(a[1..], b);
    }
  }

  lemma JoinLenUniform(parts: seq<string>, d: nat)
    requires forall k :: 0 <= k < |parts| ==> |parts[k]| == d
    ensures |Join(parts, "")| == d * |parts|
    decreases |parts|
  {
    if |parts| > 1 { JoinLenUniform(parts[1..], d); }
  }

  lemma IntToStringLen(x: int)
    requires x >= 1
    ensures 1 <= x <= 9        ==> |IntToString(x)| == 1
    ensures 10 <= x <= 99      ==> |IntToString(x)| == 2
    ensures 100 <= x <= 999    ==> |IntToString(x)| == 3
    ensures 1000 <= x <= 9999  ==> |IntToString(x)| == 4
  {
    if x >= 10 { IntToStringLen(x / 10); }
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

  // ---- min / max over a sequence ------------------------------------------
  // Accumulator-passing, so these are O(n). The naive shape
  //     if s[0] >= MaxOf(s[1..]) then s[0] else MaxOf(s[1..])
  // evaluates the recursive call in BOTH the condition and the branch, giving
  // T(n) = 2T(n-1) -- exponential. It passes tests on small inputs and blows up
  // on large ones, which is the worst way for a bug to behave in a dataset
  // whose rows carry complexity labels.

  function MaxSeqFrom(s: seq<int>, i: nat, best: int): int
    requires i <= |s|
    decreases |s| - i
  {
    if i == |s| then best
    else MaxSeqFrom(s, i + 1, if s[i] > best then s[i] else best)
  }

  function MaxSeq(s: seq<int>): int
    requires |s| > 0
  {
    MaxSeqFrom(s, 1, s[0])
  }

  function MinSeqFrom(s: seq<int>, i: nat, best: int): int
    requires i <= |s|
    decreases |s| - i
  {
    if i == |s| then best
    else MinSeqFrom(s, i + 1, if s[i] < best then s[i] else best)
  }

  function MinSeq(s: seq<int>): int
    requires |s| > 0
  {
    MinSeqFrom(s, 1, s[0])
  }

  // ---- arithmetic ---------------------------------------------------------
  // Present because translators kept writing these per file, and a local
  // reimplementation is where the exponential MaxOf/MinOf bug came from.

  function AbsInt(x: int): int { if x < 0 then -x else x }

  function SumFrom(s: seq<int>, i: nat, acc: int): int
    requires i <= |s|
    decreases |s| - i
  {
    if i == |s| then acc else SumFrom(s, i + 1, acc + s[i])
  }

  function SumSeq(s: seq<int>): int { SumFrom(s, 0, 0) }

  function Gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases b
  {
    if b == 0 then a else Gcd(b, a % b)
  }

  function Repeat(s: string, n: nat): string
    decreases n
  {
    if n == 0 then "" else s + Repeat(s, n - 1)
  }

  // Python str.replace: non-overlapping, left to right.
  function ReplaceAll(s: string, pat: string, rep: string): string
    requires |pat| > 0
    decreases |s|
  {
    if |s| < |pat| then s
    else if s[0..|pat|] == pat then rep + ReplaceAll(s[|pat|..], pat, rep)
    else [s[0]] + ReplaceAll(s[1..], pat, rep)
  }

  // ---- sorting ------------------------------------------------------------
  // Merge sort, so an O(n log n) translation stays O(n log n).

  // The length facts are `ensures` on the functions themselves, not separate
  // lemmas, so every call site gets them without a proof call. Four wave-7
  // translations had to `assume` this before it lived here.
  function Merge<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool): seq<T>
    ensures |Merge(a, b, less)| == |a| + |b|
    decreases |a| + |b|
  {
    if |a| == 0 then b
    else if |b| == 0 then a
    else if less(b[0], a[0]) then [b[0]] + Merge(a, b[1..], less)
    else [a[0]] + Merge(a[1..], b, less)
  }

  function Sort<T>(s: seq<T>, less: (T, T) -> bool): seq<T>
    ensures |Sort(s, less)| == |s|
    decreases |s|
  {
    if |s| <= 1 then s
    else Merge(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less)
  }

  // Sort is a permutation. Proved as lemmas rather than  because a
  // Dafny function has no place to put the two sequence-split hints.
  lemma MergeIsPermutation<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    ensures multiset(Merge(a, b, less)) == multiset(a) + multiset(b)
    decreases |a| + |b|
  {
    if |a| == 0 {
    } else if |b| == 0 {
    } else if less(b[0], a[0]) {
      MergeIsPermutation(a, b[1..], less);
      assert b == [b[0]] + b[1..];
    } else {
      MergeIsPermutation(a[1..], b, less);
      assert a == [a[0]] + a[1..];
    }
  }

  lemma SortIsPermutation<T>(s: seq<T>, less: (T, T) -> bool)
    ensures multiset(Sort(s, less)) == multiset(s)
    decreases |s|
  {
    if |s| <= 1 {
    } else {
      var k := |s| / 2;
      SortIsPermutation(s[..k], less);
      SortIsPermutation(s[k..], less);
      MergeIsPermutation(Sort(s[..k], less), Sort(s[k..], less), less);
      assert s == s[..k] + s[k..];
    }
  }

  // The usable corollary: sorting neither invents nor drops an element.
  lemma SortKeepsElems<T>(s: seq<T>, less: (T, T) -> bool)
    ensures forall x :: x in Sort(s, less) <==> x in s
  {
    SortIsPermutation(s, less);
    forall x ensures x in Sort(s, less) <==> x in s {
      assert multiset(Sort(s, less))[x] == multiset(s)[x];
    }
  }

  lemma SortIntsKeepsElems(s: seq<int>)
    ensures multiset(SortInts(s)) == multiset(s)
    ensures forall x :: x in SortInts(s) <==> x in s
  {
    SortKeepsElems(s, (x, y) => x < y);
    SortIsPermutation(s, (x, y) => x < y);
  }

  lemma SortStringsKeepsElems(xs: seq<string>)
    ensures multiset(SortStrings(xs)) == multiset(xs)
    ensures forall x :: x in SortStrings(xs) <==> x in xs
  {
    SortKeepsElems(xs, (a: string, b: string) => StringLess(a, b));
    SortIsPermutation(xs, (a: string, b: string) => StringLess(a, b));
  }

  function SortInts(s: seq<int>): seq<int>
    ensures |SortInts(s)| == |s|
  {
    Sort(s, (x, y) => x < y)
  }

  // ---- parsing integers ------------------------------------------------
  // Hand-written in 9 translations before this was centralized.

  function ParseInt(s: string): int
  {
    if |s| == 0 then 0
    else if s[0] == '-' then -ParseIntFrom(s, 1, 0)
    else if s[0] == '+' then ParseIntFrom(s, 1, 0)
    else ParseIntFrom(s, 0, 0)
  }

  function ParseIntFrom(s: string, i: nat, acc: int): int
    decreases |s| - i
  {
    if i >= |s| then acc
    else if '0' <= s[i] <= '9' then
      ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else acc
  }

  function ParseInts(parts: seq<string>): seq<int>
  {
    seq(|parts|, i requires 0 <= i < |parts| => ParseInt(parts[i]))
  }

  // ---- string ordering -------------------------------------------------

  predicate StringLess(a: string, b: string)
    decreases |a|
  {
    if |a| == 0 then |b| > 0
    else if |b| == 0 then false
    else if a[0] != b[0] then a[0] < b[0]
    else StringLess(a[1..], b[1..])
  }

  function SortStrings(xs: seq<string>): seq<string>
    ensures |SortStrings(xs)| == |xs|
  {
    Sort(xs, (a: string, b: string) => StringLess(a, b))
  }

  // ---- bitwise on int --------------------------------------------------
  // Dafny's `int` has no bitwise operators. Translations were casting through
  // bv64 inline; these wrap that so the width lives in one place.

  function BitOr(x: int, y: int): int
    requires 0 <= x < 0x1_0000_0000_0000_0000
    requires 0 <= y < 0x1_0000_0000_0000_0000
  {
    ((x as bv64) | (y as bv64)) as int
  }

  function BitAnd(x: int, y: int): int
    requires 0 <= x < 0x1_0000_0000_0000_0000
    requires 0 <= y < 0x1_0000_0000_0000_0000
  {
    ((x as bv64) & (y as bv64)) as int
  }

  function BitXor(x: int, y: int): int
    requires 0 <= x < 0x1_0000_0000_0000_0000
    requires 0 <= y < 0x1_0000_0000_0000_0000
  {
    ((x as bv64) ^ (y as bv64)) as int
  }
}
