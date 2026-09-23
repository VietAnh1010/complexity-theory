// 442_B. Andrey and Problem  (problem 2496, solution 2496_30)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
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
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MergeLength<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLength(a, b[1..], less);
  } else {
    MergeLength(a[1..], b, less);
  }
}

lemma SortLength<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLength(s[..|s| / 2], less);
    SortLength(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

// FormatG9 is bounded by literal constants in its own code (1000, 9, 2), not
// by n: it formats one already-computed real. Its cost is O(1).
method FormatG9(value: real) returns (s: string, ghost steps: nat)
  ensures steps <= 6100
{
  steps := 1;
  if value == 0.0 {
    s := "0";
    steps := steps + 1;
    return;
  }
  var neg := value < 0.0;
  var v := if neg then -value else value;
  var e := 0;
  var iter := 0;
  steps := steps + 3;
  while v >= 10.0 && iter < 1000
    invariant 0 <= iter <= 1000
    invariant steps <= 3 * iter + 4
    decreases 1000 - iter
  {
    v := v / 10.0;
    e := e + 1;
    iter := iter + 1;
    steps := steps + 3;
  }
  iter := 0;
  steps := steps + 1;
  while v < 1.0 && iter < 1000
    invariant 0 <= iter <= 1000
    invariant steps <= 3 * iter + 3005
    decreases 1000 - iter
  {
    v := v * 10.0;
    e := e - 1;
    iter := iter + 1;
    steps := steps + 3;
  }
  var scaled := v * 100000000.0;
  var digits := (scaled + 0.5).Floor;
  steps := steps + 2;
  if digits >= 1000000000 {
    digits := digits / 10;
    e := e + 1;
    steps := steps + 2;
  }
  var digitStr := IntToString(digits);
  IntToStringNonEmpty(digits);
  steps := steps + 1;
  var padIter := 0;
  while |digitStr| < 9 && padIter < 9
    invariant 0 <= padIter <= 9
    invariant |digitStr| >= 1
    invariant steps <= padIter + 6015
    decreases 9 - padIter
  {
    digitStr := "0" + digitStr;
    padIter := padIter + 1;
    steps := steps + 1;
  }
  var trimEnd := |digitStr|;
  steps := steps + 1;
  var trimIter := 0;
  while trimEnd > 1 && digitStr[trimEnd-1] == '0' && trimIter < 20
    invariant 1 <= trimEnd <= |digitStr|
    invariant 0 <= trimIter <= 20
    invariant steps <= trimIter + 6025
    decreases 20 - trimIter
  {
    trimEnd := trimEnd - 1;
    trimIter := trimIter + 1;
    steps := steps + 1;
  }
  var trimmed := digitStr[..trimEnd];
  assert |trimmed| >= 1;
  steps := steps + 1;

  var body: string;
  if e < -4 || e >= 9 {
    var mantissa := if |trimmed| == 1 then trimmed else trimmed[..1] + "." + trimmed[1..];
    var expSign := if e < 0 then "-" else "+";
    var expAbs := if e < 0 then -e else e;
    var expStr := IntToString(expAbs);
    steps := steps + 5;
    var expIter := 0;
    while |expStr| < 2 && expIter < 2
      invariant 0 <= expIter <= 2
      invariant steps <= expIter + 6052
      decreases 2 - expIter
    {
      expStr := "0" + expStr;
      expIter := expIter + 1;
      steps := steps + 1;
    }
    body := mantissa + "e" + expSign + expStr;
    steps := steps + 1;
  } else if e >= 0 {
    var intLen := e + 1;
    if intLen >= |trimmed| {
      body := trimmed + Repeat("0", intLen - |trimmed|);
    } else {
      body := trimmed[..intLen] + "." + trimmed[intLen..];
    }
    steps := steps + 2;
  } else {
    body := "0." + Repeat("0", -e - 1) + trimmed;
    steps := steps + 2;
  }
  s := (if neg then "-" else "") + body;
  steps := steps + 1;
}

method Solve(n: int, a_list: seq<real>) returns (output: string, ghost steps: nat)
  requires |a_list| == n
  ensures steps <= 4 * NLogN(n) + 2 + 5 * n + 6110
{
  steps := 1;
  SortCostNLogN(n);
  var ps := Sort(a_list, (x: real, y: real) => x > y);
  SortLength(a_list, (x, y) => x > y);
  steps := steps + SortCost(n);
  var hasOne := false;
  var i := 0;
  while i < |ps|
    invariant 0 <= i <= |ps|
    invariant !hasOne ==> forall k :: 0 <= k < i ==> ps[k] != 1.0
    invariant steps <= 2 * i + SortCost(n) + 1
    decreases |ps| - i
  {
    if ps[i] == 1.0 { hasOne := true; }
    i := i + 1;
    steps := steps + 2;
  }
  if hasOne {
    output := "1\n";
    steps := steps + 1;
  } else {
    assert forall k :: 0 <= k < |ps| ==> ps[k] != 1.0;
    var a: real := 0.0;
    var b: real := 1.0;
    var stopped := false;
    i := 0;
    steps := steps + 3;
    while i < |ps| && !stopped
      invariant 0 <= i <= |ps|
      invariant forall k :: 0 <= k < |ps| ==> ps[k] != 1.0
      invariant steps <= 3 * i + 2 * |ps| + SortCost(n) + 4
      decreases |ps| - i
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
      i := i + 1;
      steps := steps + 3;
    }
    var res, fsteps := FormatG9(a * b);
    steps := steps + fsteps;
    output := res + "\n";
    steps := steps + 1;
  }
}
