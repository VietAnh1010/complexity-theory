// 25_B. Phone numbers  (problem 1966, solution 1966_59)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// num = input()
//
// res = []
// if n % 2 == 0:
//     for i in range(0, n, 2):
//         res.append(num[i:i+2])
// else:
//     for i in range(0, n-3, 2):
//         res.append(num[i:i+2])
//     res.append(num[n-3:])
//
// print('-'.join(res))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// SumLen mirrors the charge table's "Join(parts, sep)" line: SumLen(parts) + |parts|.
ghost function SumLen1966(parts: seq<string>): nat
  decreases |parts|
{
  if |parts| == 0 then 0 else |parts[0]| + SumLen1966(parts[1..])
}

lemma SumLenBound1966(parts: seq<string>, B: nat)
  requires forall k :: 0 <= k < |parts| ==> |parts[k]| <= B
  ensures SumLen1966(parts) <= B * |parts|
  decreases |parts|
{
  if |parts| > 0 {
    SumLenBound1966(parts[1..], B);
  }
}

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  requires n == |s|
  requires n % 2 == 0 || n >= 3
  ensures steps <= 5 * n + 12
{
  steps := 1;
  var res: seq<string> := [];
  if n % 2 == 0 {
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant i % 2 == 0
      invariant |res| == i / 2
      invariant forall k :: 0 <= k < |res| ==> |res[k]| == 2
      invariant steps <= 3 * i + 1
      decreases n - i
    {
      res := res + [s[i..i+2]];
      i := i + 2;
      steps := steps + 3;
    }
  } else {
    var i := 0;
    while i < n - 3
      invariant 0 <= i <= n - 3
      invariant i % 2 == 0
      invariant |res| == i / 2
      invariant forall k :: 0 <= k < |res| ==> |res[k]| == 2
      invariant steps <= 3 * i + 1
      decreases (n - 3) - i
    {
      res := res + [s[i..i+2]];
      i := i + 2;
      steps := steps + 3;
    }
    res := res + [s[n-3..]];
    steps := steps + 2;
  }
  assert forall k :: 0 <= k < |res| ==> |res[k]| <= 3;
  SumLenBound1966(res, 3);
  assert |res| <= n / 2 + 1;
  output := Join(res, "-");
  steps := steps + SumLen1966(res) + |res|;
}
