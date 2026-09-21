// 1395_A. Boboniu Likes to Color Balls  (problem 1235, solution 1235_283)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def get_res(a, b, c, d):
//     if a==0 or b==0 or c==0:
//         l = [x%2 for x in [a,b,c,d]]
//         odds = sum(l)
//         if odds > 1:
//             return 'No'
//         else:
//             return 'Yes'
//     else:
//         l = [x%2 for x in [a,b,c,d]]
//         odds = sum(l)
//         if odds == 2:
//             return 'No'
//         else:
//             return 'Yes'
//
//
// n = int(input())
// for _ in range(n):
//     lis = list(map(lambda x: int(x), input().split()))
//     print(get_res(*lis))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

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

lemma SumLenBoundBy(xs: seq<string>, c: nat)
  requires forall k :: 0 <= k < |xs| ==> |xs[k]| <= c
  ensures SumLen(xs) <= c * |xs|
  decreases |xs|
{
  if |xs| > 0 { SumLenBoundBy(xs[1..], c); }
}

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n == |matrix|
  requires forall k :: 0 <= k < n ==> |matrix[k]| >= 4
  ensures steps <= 25 * n + 5
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |lines| == i
    invariant forall k :: 0 <= k < |lines| ==> |lines[k]| <= 3
    invariant steps <= 20 * i + 1
    decreases n - i
  {
    var row := matrix[i];
    var a := row[0];
    var b := row[1];
    var c := row[2];
    var d := row[3];
    var odds := 0;
    if a % 2 == 1 { odds := odds + 1; }
    if b % 2 == 1 { odds := odds + 1; }
    if c % 2 == 1 { odds := odds + 1; }
    if d % 2 == 1 { odds := odds + 1; }
    var res: string;
    if a == 0 || b == 0 || c == 0 {
      res := if odds > 1 then "No" else "Yes";
    } else {
      res := if odds == 2 then "No" else "Yes";
    }
    SumLenSnoc(lines, res);
    lines := lines + [res];
    i := i + 1;
    steps := steps + 20;
  }
  SumLenBoundBy(lines, 3);
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
}
