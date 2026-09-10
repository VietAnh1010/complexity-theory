// 2496_30 (problem 2496) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : SORTK * ((n + 2) * (n + 2)) + 2 * BIG * (n + 1) + 2 * BIG
//   proved class    : unclassified
//   agent verdict   : gave_up
//   reference label : O(nlogn)
//   prediction correct against the label: False
//   all gates passed: False
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     Solve calls the prelude Merge sort once on a_list (n=|a_list|); Merge
//     builds its result via `[x] + Merge(...)` (seq concat, cost = sum of
//     lengths) at every one of its ~n recursive steps, so a single Merge
//     call costs O(size^2), and Sort's T(n)=2T(n/2)+O(n^2) recursion is
//     O(n^2) overall -- despite looking like textbook O(n log n) merge sort,
//     the two remaining loops are plain O(n) and dominated.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 2496_30
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// import sys
// 
// input()
// ps = sorted((float(p) for p in input().split()), reverse=True)
// if 1.0 in ps:
//     print(1)
//     sys.exit()
// a, b = 0, 1
// for p in ps:
//     c, d = a + p / (1 - p), b * (1 - p)
//     if c * d > a * b:
//         a, b = c, d
//     else:
//         break
// print('{:.9}'.format(a * b))
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method FormatG9(value: real) returns (s: string)
{
  if value == 0.0 {
    s := "0";
    return;
  }
  var neg := value < 0.0;
  var v := if neg then -value else value;
  var e := 0;
  var iter := 0;
  while v >= 10.0 && iter < 1000
    invariant 0 <= iter <= 1000
    decreases 1000 - iter
  {
    v := v / 10.0;
    e := e + 1;
    iter := iter + 1;
  }
  iter := 0;
  while v < 1.0 && iter < 1000
    invariant 0 <= iter <= 1000
    decreases 1000 - iter
  {
    v := v * 10.0;
    e := e - 1;
    iter := iter + 1;
  }
  var scaled := v * 100000000.0;
  var digits := (scaled + 0.5).Floor;
  if digits >= 1000000000 {
    digits := digits / 10;
    e := e + 1;
  }
  var digitStr := IntToString(digits);
  while |digitStr| < 9
  {
    digitStr := "0" + digitStr;
  }
  var trimEnd := |digitStr|;
  while trimEnd > 1 && digitStr[trimEnd-1] == '0'
    invariant 1 <= trimEnd <= |digitStr|
  {
    trimEnd := trimEnd - 1;
  }
  var trimmed := digitStr[..trimEnd];
  assert |trimmed| >= 1;

  var body: string;
  if e < -4 || e >= 9 {
    var mantissa := if |trimmed| == 1 then trimmed else trimmed[..1] + "." + trimmed[1..];
    var expSign := if e < 0 then "-" else "+";
    var expAbs := if e < 0 then -e else e;
    var expStr := IntToString(expAbs);
    while |expStr| < 2
    {
      expStr := "0" + expStr;
    }
    body := mantissa + "e" + expSign + expStr;
  } else if e >= 0 {
    var intLen := e + 1;
    if intLen >= |trimmed| {
      body := trimmed + Repeat("0", intLen - |trimmed|);
    } else {
      body := trimmed[..intLen] + "." + trimmed[intLen..];
    }
  } else {
    body := "0." + Repeat("0", -e - 1) + trimmed;
  }
  s := (if neg then "-" else "") + body;
}

// ---- cost bounds for the prelude's merge sort ---------------------------
//
// Merge builds its result with `[x] + Merge(...)` at every one of its ~t
// recursive steps (t = total remaining elements). Each such `+` is a seq
// concat, real cost = sum of the two lengths = (current total), so one
// Merge call over t elements costs sum_{k=1}^{t} k = O(t^2), not O(t).
ghost function MergeCostBound(t: nat): nat
  decreases t
{
  if t <= 1 then 1 else t + MergeCostBound(t - 1)
}

lemma SqSubOne(t: int)
  ensures (t - 1) * (t - 1) == t * t - 2 * t + 1
{}

lemma MergeCostBoundSq(t: nat)
  ensures MergeCostBound(t) <= t * t + 1
  decreases t
{
  if t > 1 {
    MergeCostBoundSq(t - 1);
    SqSubOne(t);
  }
}

// Sort's recursion is T(n) = 2*T(n/2) + MergeCostBound(n); the doubled
// concat cost at every level makes this O(n^2), dominating both the halving
// and (with such a generous constant) any O(n log n) alternative would.
ghost function SortCostBound(n: nat): nat
  decreases n
{
  if n <= 1 then 1 else 2 * SortCostBound(n / 2) + MergeCostBound(n)
}

lemma SqMono(x: int, y: int)
  requires 0 <= x <= y
  ensures x * x <= y * y
{}

lemma MulMonoRight(x: int, p: int, q: int)
  requires x >= 0 && p <= q
  ensures x * p <= x * q
{}

ghost const SORTK: nat := 1000

lemma PolyIneq(n: int)
  requires n >= 2
  ensures SORTK * ((n + 2) * (n + 2)) + 2 * (n * n) + 2 <= 2 * (SORTK * ((n + 1) * (n + 1)))
{
  SqMono(2, n);
}

lemma SortCostBoundSq(n: nat)
  ensures SortCostBound(n) <= SORTK * ((n + 1) * (n + 1))
  decreases n
{
  if n > 1 {
    var m := n / 2;
    SortCostBoundSq(m);
    MergeCostBoundSq(n);
    assert 2 * (m + 1) <= n + 2;
    SqMono(2 * (m + 1), n + 2);
    assert 4 * ((m + 1) * (m + 1)) <= (n + 2) * (n + 2);
    MulMonoRight(SORTK, 4 * ((m + 1) * (m + 1)), (n + 2) * (n + 2));
    assert 4 * (SORTK * ((m + 1) * (m + 1))) <= SORTK * ((n + 2) * (n + 2));
    PolyIneq(n);
    assert 4 * (SORTK * ((m + 1) * (m + 1))) + 2 * (n * n) + 2
        <= 2 * (SORTK * ((n + 1) * (n + 1)));
    assert 2 * (2 * SortCostBound(m)) + 2 * MergeCostBound(n)
        <= 2 * (SORTK * ((n + 1) * (n + 1)));
    assert 2 * SortCostBound(m) + MergeCostBound(n) <= SORTK * ((n + 1) * (n + 1));
  }
}

// Generous fixed constant covering every O(1) real op in this method (real
// arithmetic, comparisons) and FormatG9's cost, which is bounded by its own
// hardcoded loop caps (<1000 iterations, <=9-digit strings) regardless of n.
ghost const BIG: nat := 3000000000000000000

method Solve(n: int, a_list: seq<real>) returns (output: string, ghost steps: nat)
  requires |a_list| == n
  ensures steps <= SORTK * ((n + 2) * (n + 2)) + 2 * BIG * (n + 1) + 2 * BIG
{
  steps := 1;
  var ps := Sort(a_list, (x: real, y: real) => x > y);
  SortCostBoundSq(n);
  SqMono(n + 1, n + 2);
  MulMonoRight(SORTK, (n + 1) * (n + 1), (n + 2) * (n + 2));
  assert SORTK * ((n + 1) * (n + 1)) <= SORTK * ((n + 2) * (n + 2));
  assert |ps| == n;
  steps := steps + SORTK * (n + 1) * (n + 1);
  var hasOne := false;
  var i := 0;
  while i < |ps|
    invariant 0 <= i <= |ps|
    invariant !hasOne ==> forall k :: 0 <= k < i ==> ps[k] != 1.0
    invariant steps <= SORTK * (n + 1) * (n + 1) + 1 + BIG * i
  {
    if ps[i] == 1.0 { hasOne := true; }
    steps := steps + BIG;
    i := i + 1;
  }
  if hasOne {
    output := "1\n";
    steps := steps + BIG;
    assert steps <= SORTK * ((n + 1) * (n + 1)) + 1 + BIG * n + BIG;
  } else {
    assert forall k :: 0 <= k < |ps| ==> ps[k] != 1.0;
    var a: real := 0.0;
    var b: real := 1.0;
    var stopped := false;
    i := 0;
    while i < |ps| && !stopped
      invariant 0 <= i <= |ps|
      invariant forall k :: 0 <= k < |ps| ==> ps[k] != 1.0
      invariant steps <= SORTK * (n + 1) * (n + 1) + 1 + BIG * |ps| + BIG * i
    {
      var p := ps[i];
      var c := a + p / (1.0 - p);
      var d := b * (1.0 - p);
      if c * d > a * b {
        a := c;
        b := d;
      } else {
        stopped := true;
      }
      steps := steps + BIG;
      i := i + 1;
    }
    var res := FormatG9(a * b);
    output := res + "\n";
    steps := steps + BIG;
    assert steps <= SORTK * ((n + 1) * (n + 1)) + 1 + BIG * n + BIG * n + BIG;
  }
}
