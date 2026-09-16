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

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}

// Label O(n). One pass building the map (each token parsed as an O(1)
// value lookup / insert), then one pass draining its key set: each
// iteration removes one key, so it also runs |d.Keys| <= |a_list| times.
method Solve(n: int, a_list: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |a_list| + 3
{
  steps := 1;
  var d: map<int, int> := map[];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant |d.Keys| <= i
    invariant steps <= 3 * i + 1
    decreases |a_list| - i
  {
    var a := ParseInt(a_list[i]);
    if a in d {
      d := d[a := d[a] + 1];
    } else {
      assert d[a := 1].Keys == d.Keys + {a};
      d := d[a := 1];
    }
    i := i + 1;
    steps := steps + 3;
  }
  var maxn := 0;
  var keys := d.Keys;
  while keys != {}
    invariant keys <= d.Keys
    invariant |keys| <= |a_list|
    invariant steps <= 3 * |a_list| + 1 + (|a_list| - |keys|)
    decreases |keys|
  {
    var k :| k in keys;
    if d[k] > maxn { maxn := d[k]; }
    keys := keys - {k};
    steps := steps + 1;
  }
  output := IntToString(maxn);
  steps := steps + 1;
}
