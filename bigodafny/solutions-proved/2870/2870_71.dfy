// 1463_A. Dungeon  (problem 2870, solution 2870_71)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// T = int(input())
// for i in range(0, T) :
//     a, b, c = input().split()
//     a = int(a)
//     b = int(b)
//     c = int(c)
//     Sum = a + b + c
//     if Sum % 9 == 0 and Sum / 9 <= min(a, min(b, c)) :
//         print("YES")
//     else :
//         print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function TotLen(v: seq<seq<int>>, i: nat): nat
  requires i <= |v|
  decreases i
{
  if i == 0 then 0 else TotLen(v, i - 1) + |v[i - 1]|
}

lemma TotLenStep(v: seq<seq<int>>, i: nat)
  requires i < |v|
  ensures TotLen(v, i + 1) == TotLen(v, i) + |v[i]|
{}

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires |values_list| == n
  requires forall k :: 0 <= k < |values_list| ==> |values_list[k]| > 0
  ensures steps <= 20 * n + 2 * TotLen(values_list, n) + 5
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |lines| == i
    invariant SumLen(lines) <= 3 * i
    invariant steps <= 1 + 14 * i + 2 * TotLen(values_list, i)
  {
    var s := values_list[i];
    TotLenStep(values_list, i);
    steps := steps + 14 + 2 * |s|;
    var sm := SumSeq(s);
    var mn := MinSeq(s);
    if sm % 9 == 0 && mn >= sm / 9 {
      SumLenSnoc(lines, "YES");
      lines := lines + ["YES"];
    } else {
      SumLenSnoc(lines, "NO");
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  steps := steps + SumLen(lines) + |lines| + 1;
  output := if |lines| > 0 then Join(lines, "\n") + "\n" else "";
}
