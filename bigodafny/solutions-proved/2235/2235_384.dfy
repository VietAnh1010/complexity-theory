// 1400_A. String Similarity  (problem 2235, solution 2235_384)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #872
// for _ in range(int(input())):
//     n=int(input())
//     a=input()
//     print(a[::2])
//
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Total characters across the first k processed lines: the quantity the
// label's "n" really tracks here (t itself only counts lines).
ghost function TotalLen(strs: seq<string>, k: nat): nat
  requires k <= |strs|
  decreases k
{
  if k == 0 then 0 else TotalLen(strs, k - 1) + |strs[k - 1]|
}

method Solve(t: int, n_list: seq<int>, s_list: seq<string>) returns (output: string, ghost steps: nat)
  requires t <= |s_list|
  requires t >= 0
  ensures steps <= 5 * TotalLen(s_list, t) + 10 * t + 10
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant |lines| == i
    invariant steps == 5 * TotalLen(s_list, i) + 4 * i + 1
    decreases t - i
  {
    var s := s_list[i];
    var res: seq<char> := [];
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
      invariant steps == 5 * TotalLen(s_list, i) + 4 * i + 1 + 5 * j
      decreases |s| - j
    {
      if j % 2 == 0 { res := res + [s[j]]; }
      j := j + 1;
      steps := steps + 5;
    }
    lines := lines + [res];
    assert TotalLen(s_list, i + 1) == TotalLen(s_list, i) + |s_list[i]|;
    i := i + 1;
    steps := steps + 4;
  }
  output := Join(lines, "\n");
  steps := steps + |lines| + 1;
  assert |lines| == t;
  assert steps <= 5 * TotalLen(s_list, t) + 4 * t + 1 + t + 1;
}
