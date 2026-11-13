include "../../prelude.dfy"
import opened Prelude

function ReverseSeq(s: seq<int>): seq<int>
  ensures |ReverseSeq(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseSeq(s[1..]) + [s[0]]
}

function FindMinIndexFrom(s: seq<int>, i: int, best: int): int
  requires 0 <= best < |s|
  requires 0 <= i <= |s|
  ensures 0 <= FindMinIndexFrom(s, i, best) < |s|
  decreases |s| - i
{
  if i == |s| then best
  else if s[i] < s[best] then FindMinIndexFrom(s, i + 1, i)
  else FindMinIndexFrom(s, i + 1, best)
}

function FindMinIndex(s: seq<int>): int
  requires |s| > 0
  ensures 0 <= FindMinIndex(s) < |s|
{
  FindMinIndexFrom(s, 1, 0)
}

function RemoveAt(s: seq<int>, idx: int): seq<int>
  requires 0 <= idx < |s|
  ensures |RemoveAt(s, idx)| == |s| - 1
{
  s[..idx] + s[idx + 1..]
}

ghost function C1f(n: nat): nat { 8 * n + 10 }
ghost function C2f(n: nat): nat { n * C1f(n) + 6 * n + 40 }

method Solve(n: int, a_list: seq<int>, q: int, queries: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires forall qq :: 0 <= qq < |queries| ==> 1 <= queries[qq].0 <= n
  ensures steps <= |queries| * C2f(n) + 2 * |output| + 5
{
  steps := 1;
  ghost var C1 := C1f(n);
  ghost var C2 := C2f(n);
  var parts: seq<string> := [];
  var qi := 0;
  while qi < |queries|
    invariant 0 <= qi <= |queries|
    invariant steps <= 1 + qi * C2 + SumLen(parts)
    decreases |queries| - qi
  {
    var kk := queries[qi].0;
    var pos := queries[qi].1;
    ghost var sq := steps;
    var ai := ReverseSeq(a_list);
    steps := steps + 3 * n + 2;
    var removeCount := if n - kk > 0 then n - kk else 0;
    var jcount := 0;
    ghost var s0 := steps;
    while jcount < removeCount
      invariant 0 <= jcount <= removeCount
      invariant |ai| == n - jcount
      invariant removeCount <= n
      invariant steps <= s0 + jcount * C1
      decreases removeCount - jcount
    {
      var mi := FindMinIndex(ai);
      ai := RemoveAt(ai, mi);
      steps := steps + C1;
      CostMulDistrib(jcount, 1, jcount + 1, C1);
      jcount := jcount + 1;
    }
    CostMulMonoLeft(jcount, n, C1);
    ai := ReverseSeq(ai);
    steps := steps + 3 * n + 12;
    if 0 <= pos - 1 < |ai| {
      ghost var part := "\n" + IntToString(ai[pos - 1]);
      SumLenSnoc(parts, part);
      parts := parts + ["\n" + IntToString(ai[pos - 1])];
    }
    CostMulDistrib(qi, 1, qi + 1, C2);
    qi := qi + 1;
  }
  output := Join(parts, "") + "\n";
  JoinLen(parts, "");
  steps := steps + SumLen(parts) + |parts| + 1;
  CostMulMonoLeft(|parts|, |queries|, C2);
}
