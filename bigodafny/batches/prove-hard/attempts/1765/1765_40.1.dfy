// --- Python ---------------------------------------------------------
// size = int(input())
// data = [int(x) for x in input().split()]
// error = False
// while size > 1:
//     for i in range(size - 1):
//         if abs(data[i] - data[i+1]) >= 2:
//             error = True
//     data.remove(max(data))
//     size -= 1
// print("NO" if error else "YES")
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma MaxSeqFromIn1765(s: seq<int>, i: nat, best: int)
  requires i <= |s|
  ensures MaxSeqFrom(s, i, best) == best || exists k :: i <= k < |s| && MaxSeqFrom(s, i, best) == s[k]
  decreases |s| - i
{
  if i < |s| {
    MaxSeqFromIn1765(s, i + 1, if s[i] > best then s[i] else best);
  }
}

lemma MaxSeqIn1765(s: seq<int>)
  requires |s| > 0
  ensures exists k :: 0 <= k < |s| && MaxSeq(s) == s[k]
{
  MaxSeqFromIn1765(s, 1, s[0]);
}

lemma MulStep1765(a: nat, k: nat)
  ensures (a + 1) * k == a * k + k
{}

lemma MulMono1765(a: nat, b: nat, k: nat)
  requires a <= b
  ensures a * k <= b * k
{}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= n * (20 * n + 20) + 2
{
  steps := 0;
  var size := n;
  var data := a_list;
  var error := false;
  ghost var iters: nat := 0;
  while size > 1
    invariant |data| == size
    invariant 0 <= size <= n
    invariant iters == n - size
    invariant steps <= iters * (20 * n + 20)
    decreases size
  {
    ghost var s0 := steps;
    steps := steps + 2;
    var i := 0;
    while i < size - 1
      invariant 0 <= i <= size - 1
      invariant steps <= s0 + 2 + 11 * i
      decreases size - 1 - i
    {
      steps := steps + 3;
      steps := steps + (5 + 1);
      if AbsInt(data[i] - data[i + 1]) >= 2 {
        error := true;
      }
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + 2;
    steps := steps + |data|;
    var mx := MaxSeq(data);
    MaxSeqIn1765(data);
    var idx := 0;
    ghost var s1 := steps;
    while idx < size && data[idx] != mx
      invariant 0 <= idx <= size
      invariant steps <= s1 + 6 * idx
      invariant exists k :: idx <= k < size && data[k] == mx
      decreases size - idx
    {
      steps := steps + (3 + if idx < size then 2 else 0);
      steps := steps + 1;
      idx := idx + 1;
    }
    steps := steps + (2 + if idx < size then 2 else 0);
    assert idx < size;
    steps := steps + (3 + |data[idx + 1..]|);
    data := data[0 .. idx] + data[idx + 1..];
    steps := steps + 1;
    size := size - 1;
    MulStep1765(iters, 20 * n + 20);
    iters := iters + 1;
  }
  MulMono1765(iters, n, 20 * n + 20);
  steps := steps + 1;
  steps := steps + 1;
  output := if error then "NO" else "YES";
}

import opened Prelude
