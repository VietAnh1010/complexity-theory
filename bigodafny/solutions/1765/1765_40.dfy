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

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
  var size := n;
  var data := a_list;
  var error := false;
  while size > 1
    invariant |data| == size
    decreases size
  {
    var i := 0;
    while i < size - 1
      invariant 0 <= i <= size - 1
      decreases size - 1 - i
    {
      if AbsInt(data[i] - data[i + 1]) >= 2 {
        error := true;
      }
      i := i + 1;
    }
    var mx := MaxSeq(data);
    MaxSeqIn1765(data);
    var idx := 0;
    while idx < size && data[idx] != mx
      invariant 0 <= idx <= size
      invariant exists k :: idx <= k < size && data[k] == mx
      decreases size - idx
    {
      idx := idx + 1;
    }
    assert idx < size;
    data := data[0..idx] + data[idx + 1..];
    size := size - 1;
  }
  output := if error then "NO" else "YES";
}
