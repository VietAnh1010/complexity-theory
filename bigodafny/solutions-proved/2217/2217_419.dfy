// 501_B. Misha and Changing Handles  (problem 2217, solution 2217_419)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// d = {}
// for i in range(t):
//     old,new = input().split()
//     d[new] = d.get(old,old)
//     if old in d:
//     	d.pop(old)
// print(len(d))
// for a,b in d.items():
//     print(b,a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function TotS(v: seq<string>, i: nat): nat
  requires i <= |v|
  decreases i
{
  if i == 0 then 0 else TotS(v, i - 1) + |v[i - 1]|
}

lemma TotSStep(v: seq<string>, i: nat)
  requires i < |v|
  ensures TotS(v, i + 1) == TotS(v, i) + |v[i]|
{}

method Solve(n: int, handles: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 40 * |handles| + 2 * TotS(handles, |handles|) + 2 * |output| + 10
{
  steps := 1;
  // d maps a key to (value, insertion stamp); order lists (key, stamp) in
  // insertion order, so the output follows Python's dict order.
  var d: map<string, (string, int)> := map[];
  var order: seq<(string, int)> := [];
  var i := 0;
  while i < |handles|
    invariant 0 <= i <= |handles|
    invariant |order| <= i
    invariant steps <= 1 + 30 * i + 2 * TotS(handles, i)
    decreases |handles| - i
  {
    TotSStep(handles, i);
    steps := steps + 30 + 2 * |handles[i]|;
    var parts := SplitWs(handles[i]);
    var oldh := if |parts| >= 1 then parts[0] else "";
    var newh := if |parts| >= 2 then parts[1] else "";
    var val := if oldh in d then d[oldh].0 else oldh;
    if newh in d {
      d := d[newh := (val, d[newh].1)];
    } else {
      d := d[newh := (val, i)];
      order := order + [(newh, i)];
    }
    if oldh in d {
      d := d - {oldh};
    }
    i := i + 1;
  }
  var parts2: seq<string> := [];
  var m := 0;
  steps := steps + 2;
  ghost var S1 := steps;
  while m < |order|
    invariant 0 <= m <= |order|
    invariant |parts2| <= m
    invariant steps <= S1 + 9 * m + SumLen(parts2)
    decreases |order| - m
  {
    steps := steps + 9;
    var k := order[m].0;
    if k in d && d[k].1 == order[m].1 {
      SumLenSnoc(parts2, d[k].0 + " " + k);
      steps := steps + 1 + |k|;
      parts2 := parts2 + [d[k].0 + " " + k];
    }
    m := m + 1;
  }
  steps := steps + 4 + SumLen(parts2) + |parts2| + Digits(|d|);
  IntToStringDigits(|d|);
  if |parts2| > 0 { JoinLen(parts2, "\n"); }
  output := IntToString(|d|) + "\n" + (if |parts2| == 0 then "" else Join(parts2, "\n") + "\n");
}
