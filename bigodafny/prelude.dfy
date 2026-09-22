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

  // ---- prefix sums --------------------------------------------------------
  // The sliding-window rows run two pointers over `a + a`. Safety there is a
  // statement about window sums, not about the loop counters.

  ghost function PrefixSum(s: seq<int>, t: nat): int
    requires t <= |s|
    decreases t
  {
    if t == 0 then 0 else PrefixSum(s, t - 1) + s[t - 1]
  }

  lemma SumFromIsPrefixSum(s: seq<int>, i: nat, acc: int)
    requires i <= |s|
    ensures SumFrom(s, i, acc) == acc + PrefixSum(s, |s|) - PrefixSum(s, i)
    decreases |s| - i
  {
    if i < |s| { SumFromIsPrefixSum(s, i + 1, acc + s[i]); }
  }

  lemma PrefixSumIsSumSeq(s: seq<int>)
    ensures PrefixSum(s, |s|) == SumSeq(s)
  {
    SumFromIsPrefixSum(s, 0, 0);
  }

  lemma PrefixSumDoubledLo(a: seq<int>, t: nat)
    requires t <= |a|
    ensures PrefixSum(a + a, t) == PrefixSum(a, t)
    decreases t
  {
    if t > 0 { PrefixSumDoubledLo(a, t - 1); }
  }

  lemma PrefixSumDoubledHi(a: seq<int>, t: nat)
    requires |a| <= t <= 2 * |a|
    ensures PrefixSum(a + a, t) == PrefixSum(a, |a|) + PrefixSum(a, t - |a|)
    decreases t
  {
    if t == |a| { PrefixSumDoubledLo(a, t); }
    else { PrefixSumDoubledHi(a, t - 1); }
  }

  // any |a| consecutive entries of `a + a` sum to the whole of `a`
  lemma PrefixSumWindowDoubled(a: seq<int>, i: nat)
    requires i <= |a|
    ensures PrefixSum(a + a, i + |a|) - PrefixSum(a + a, i)
         == PrefixSum(a, |a|)
  {
    PrefixSumDoubledLo(a, i);
    PrefixSumDoubledHi(a, i + |a|);
  }

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

  // ---- sortedness ---------------------------------------------------------
  // Added 2026-09-22. Until then the only thing proved about Sort was that it
  // is a permutation -- the output holds the same elements as the input --
  // and nothing said the output was in ORDER. So no proof could say "the last
  // element after sorting is the largest", and a loop whose trip count is
  // `sorted[-1]` could not even be named, let alone bounded. That is what
  // stopped solutions/2423/2423_48.dfy; see
  // batches/value-bounded-open/README.md.
  //
  // `less` must be a strict total order for any of this to hold. The
  // requirement is explicit rather than assumed: Merge picks b[0] when
  // less(b[0], a[0]) and a[0] otherwise, so without totality a "tie" that is
  // neither less nor equal breaks sortedness, and without irreflexivity an
  // element is not <= itself.
  ghost predicate StrictTotalOrder<T(!new)>(less: (T, T) -> bool)
  {
    && (forall x: T :: !less(x, x))
    && (forall x: T, y: T, z: T :: less(x, y) && less(y, z) ==> less(x, z))
    && (forall x: T, y: T :: x != y ==> less(x, y) || less(y, x))
  }

  ghost predicate IsSorted<T>(s: seq<T>, less: (T, T) -> bool)
  {
    forall i, j :: 0 <= i < j < |s| ==> !less(s[j], s[i])
  }

  lemma MergeElems<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    ensures forall x :: x in Merge(a, b, less) <==> x in a || x in b
  {
    MergeIsPermutation(a, b, less);
    forall x ensures x in Merge(a, b, less) <==> x in a || x in b {
      assert multiset(Merge(a, b, less))[x] == multiset(a)[x] + multiset(b)[x];
    }
  }

  lemma HeadIsMin<T(!new)>(s: seq<T>, less: (T, T) -> bool)
    requires StrictTotalOrder(less)   // irreflexivity is what covers x == s[0]
    requires IsSorted(s, less)
    requires |s| > 0
    ensures forall x :: x in s ==> !less(x, s[0])
  {
    forall x | x in s ensures !less(x, s[0]) {
      var i :| 0 <= i < |s| && s[i] == x;
      if i > 0 { assert !less(s[i], s[0]); }
    }
  }

  lemma LastIsMax<T(!new)>(s: seq<T>, less: (T, T) -> bool)
    requires StrictTotalOrder(less)
    requires IsSorted(s, less)
    requires |s| > 0
    ensures forall x :: x in s ==> !less(s[|s| - 1], x)
  {
    forall x | x in s ensures !less(s[|s| - 1], x) {
      var i :| 0 <= i < |s| && s[i] == x;
      if i < |s| - 1 { assert !less(s[|s| - 1], s[i]); }
    }
  }

  lemma ConsSorted<T>(h: T, t: seq<T>, less: (T, T) -> bool)
    requires IsSorted(t, less)
    requires forall x :: x in t ==> !less(x, h)
    ensures IsSorted([h] + t, less)
  {
    var s := [h] + t;
    forall i, j | 0 <= i < j < |s| ensures !less(s[j], s[i]) {
      if i == 0 { assert s[j] in t; }
      else { assert s[i] == t[i-1] && s[j] == t[j-1]; }
    }
  }

  lemma MergeIsSorted<T(!new)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires StrictTotalOrder(less)
    requires IsSorted(a, less) && IsSorted(b, less)
    ensures IsSorted(Merge(a, b, less), less)
    decreases |a| + |b|
  {
    if |a| == 0 || |b| == 0 { return; }
    if less(b[0], a[0]) {
      MergeIsSorted(a, b[1..], less);
      MergeElems(a, b[1..], less);
      HeadIsMin(a, less);
      HeadIsMin(b, less);
      forall x | x in Merge(a, b[1..], less) ensures !less(x, b[0]) {
        if x in a {
          assert !less(x, a[0]);
          if less(x, b[0]) { assert less(x, a[0]); }   // b[0] < a[0] <= x
        } else {
          assert x in b[1..];
          assert x in b;
        }
      }
      ConsSorted(b[0], Merge(a, b[1..], less), less);
    } else {
      MergeIsSorted(a[1..], b, less);
      MergeElems(a[1..], b, less);
      HeadIsMin(a, less);
      HeadIsMin(b, less);
      forall x | x in Merge(a[1..], b, less) ensures !less(x, a[0]) {
        if x in a[1..] { assert x in a; }
        else {
          assert x in b;
          assert !less(x, b[0]);
          if less(x, a[0]) { assert !less(b[0], a[0]); }
        }
      }
      ConsSorted(a[0], Merge(a[1..], b, less), less);
    }
  }

  lemma SortIsSorted<T(!new)>(s: seq<T>, less: (T, T) -> bool)
    requires StrictTotalOrder(less)
    ensures IsSorted(Sort(s, less), less)
    decreases |s|
  {
    if |s| <= 1 { return; }
    var k := |s| / 2;
    SortIsSorted(s[..k], less);
    SortIsSorted(s[k..], less);
    MergeIsSorted(Sort(s[..k], less), Sort(s[k..], less), less);
  }

  // The usable corollary, and the one 2423_48 needs: after sorting, the last
  // element is >= every element of the original sequence. A loop bounded by
  // `sorted[|sorted|-1]` can now be tied back to the input.
  lemma SortLastIsMax<T(!new)>(s: seq<T>, less: (T, T) -> bool)
    requires StrictTotalOrder(less)
    requires |s| > 0
    ensures |Sort(s, less)| == |s|
    ensures forall x :: x in s ==> !less(Sort(s, less)[|s| - 1], x)
  {
    SortIsSorted(s, less);
    SortKeepsElems(s, less);
    LastIsMax(Sort(s, less), less);
  }

  // int is the common case, so the order obligation is discharged once here.
  lemma IntLessIsTotalOrder()
    ensures StrictTotalOrder<int>((x, y) => x < y)
  {}

  lemma SortIntsIsSorted(s: seq<int>)
    ensures IsSorted(SortInts(s), (x, y) => x < y)
    ensures |SortInts(s)| == |s|
    ensures |s| > 0 ==> forall x :: x in s ==> SortInts(s)[|s| - 1] >= x
  {
    IntLessIsTotalOrder();
    SortIsSorted(s, (x, y) => x < y);
    if |s| > 0 { SortLastIsMax(s, (x, y) => x < y); }
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
