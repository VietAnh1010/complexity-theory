// 1003_A. Polycarp's Pockets  (problem 976, solution 976_1131)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = list(map(int, input().split()))
// 
// d = dict()
// for a in arr:
//     if not a in d:
//         d[a] = 0
//     d[a] += 1
// 
// maxn = 0
// for a in d:
//     maxn = max(maxn, d[a])
// 
// print(maxn)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var d: map<int, int> := map[];
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var a := ParseInt(a_list[i]);
    if a in d {
      d := d[a := d[a] + 1];
    } else {
      d := d[a := 1];
    }
    i := i + 1;
  }
  var maxn := 0;
  var keys := d.Keys;
  while keys != {}
    invariant keys <= d.Keys
    decreases |keys|
  {
    var k :| k in keys;
    if d[k] > maxn { maxn := d[k]; }
    keys := keys - {k};
  }
  output := IntToString(maxn);
}
