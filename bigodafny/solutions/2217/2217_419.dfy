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

method Solve(n: int, handles: seq<string>) returns (output: string)
{
  // d maps a key to (value, insertion stamp); order lists (key, stamp) in
  // insertion order, so the output follows Python's dict order.
  var d: map<string, (string, int)> := map[];
  var order: seq<(string, int)> := [];
  var i := 0;
  while i < |handles|
    invariant 0 <= i <= |handles|
  {
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
  while m < |order|
  {
    var k := order[m].0;
    if k in d && d[k].1 == order[m].1 {
      parts2 := parts2 + [d[k].0 + " " + k];
    }
    m := m + 1;
  }
  output := IntToString(|d|) + "\n" + (if |parts2| == 0 then "" else Join(parts2, "\n") + "\n");
}
