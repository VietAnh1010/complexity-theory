// 952_C. Ravioli Sort  (problem 1765, solution 1765_40)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

// MaxSeqFrom either keeps the running best or returns some element it saw.
lemma MaxSeqFromIn1765(s: seq<int>, i: nat, best: int)
  requires i <= |s|
  ensures MaxSeqFrom(s, i, best) == best
       || exists k :: i <= k < |s| && MaxSeqFrom(s, i, best) == s[k]
  decreases |s| - i
{
  if i < |s| { MaxSeqFromIn1765(s, i + 1, if s[i] > best then s[i] else best); }
}

lemma MaxSeqIn1765(s: seq<int>)
  requires |s| > 0
  ensures exists k :: 0 <= k < |s| && MaxSeq(s) == s[k]
{
  MaxSeqFromIn1765(s, 1, s[0]);
}

lemma MulDistribStep(m: nat, B: nat)
  ensures (m + 1) * B == m * B + B
{ }

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 0
  ensures steps <= n * (10 * n + 10) + 2
{
  var size := n;
  var data := a_list;
  var error := false;
  ghost var B := 10 * n + 10;
  steps := 1;
  while size > 1
    invariant 0 <= size <= n
    invariant |data| == size
    invariant steps <= (n - size) * B + 1
    decreases size
  {
    ghost var oldSize := size;
    ghost var stepsBefore := steps;
    var i := 0;
    while i < size - 1
      invariant 0 <= i <= size - 1
      invariant steps <= stepsBefore + 4 * i
      decreases size - 1 - i
    {
      if AbsInt(data[i] - data[i + 1]) >= 2 {
        error := true;
      }
      i := i + 1;
      steps := steps + 4;
    }
    var mx := MaxSeq(data);
    MaxSeqIn1765(data);
    steps := steps + size;
    var idx := 0;
    ghost var stepsBefore2 := steps;
    while idx < size && data[idx] != mx
      invariant 0 <= idx <= size
      invariant exists k :: idx <= k < size && data[k] == mx
      invariant steps <= stepsBefore2 + 2 * idx
      decreases size - idx
    {
      idx := idx + 1;
      steps := steps + 2;
    }
    assert idx < size;
    data := data[0..idx] + data[idx + 1..];
    steps := steps + size;
    size := size - 1;
    steps := steps + 1;
    assert steps <= stepsBefore + 8 * oldSize;
    assert 8 * oldSize <= B;
    MulDistribStep(n - oldSize, B);
    assert (n - oldSize + 1) * B == (n - oldSize) * B + B;
  }
  output := if error then "NO" else "YES";
  steps := steps + 1;
}
