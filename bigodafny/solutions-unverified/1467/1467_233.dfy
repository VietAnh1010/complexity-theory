// 672_A. Summer Camp  (problem 1467, solution 1467_233)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// t=''
// for i in range(n+100):
//     t+=str(i)
// print(t[n])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma IntToStringLen(x: int)
  ensures |IntToString(x)| >= 1
  decreases if x < 0 then 1 - x else x
{
  if x < 0 { IntToStringLen(-x); }
  else if x < 10 {
  } else {
    IntToStringLen(x / 10);
  }
}

lemma JoinEmptySepLen(parts: seq<string>)
  requires forall k :: 0 <= k < |parts| ==> |parts[k]| >= 1
  ensures |Join(parts, "")| >= |parts|
  decreases |parts|
{
  if |parts| == 0 {
  } else if |parts| == 1 {
  } else {
    JoinEmptySepLen(parts[1..]);
  }
}

method Solve(N: int) returns (output: string)
  requires N >= 0
{
  var parts: seq<string> := [];
  var i := 0;
  while i < N + 100
    invariant 0 <= i
    invariant |parts| == i
    invariant forall k :: 0 <= k < |parts| ==> |parts[k]| >= 1
    decreases N + 100 - i
  {
    IntToStringLen(i);
    parts := parts + [IntToString(i)];
    i := i + 1;
  }
  JoinEmptySepLen(parts);
  var t := Join(parts, "");
  output := [t[N]];
}
