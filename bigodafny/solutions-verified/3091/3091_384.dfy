// 467_A. George and Accommodation  (problem 3091, solution 3091_384)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=[]
// count=0
// for x in range(n):
//     a+=list(map(int,input().split()))
// i=0
// while i<n*2:
//     if abs(a[i]-a[i+1])>=2:
//         count+=1
//     i+=2
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(n*m), and here it is RIGHT. `a` accumulates every token of every row
// and the second loop walks all of them, so the cost is linear in the TOTAL
// input size -- n*m when each row has width m -- not in the row count alone.
//
// Charging note. `a := a + pairs_list[i]` is charged |pairs_list[i]|, not |a|.
// Measured, in Dafny 4.11.0's Python backend: seq concatenation builds a lazy
// node and only flattens when an element is read, so appending in a loop that
// never indexes the accumulator is linear overall, and the one flatten the
// second loop forces costs |a| -- exactly the sum this charges. Reading an
// element BETWEEN appends is what makes the pattern quadratic:
//   append only:      n=8k .053s  16k .067s  32k .095s  64k .149s   (linear)
//   append + s[i]:    n=8k .126s  16k .365s  32k 1.725s 64k 7.876s  (quadratic)
// Taking |s| between appends does not flatten and stays linear.
ghost function TotalLenUpTo(rows: seq<seq<int>>, k: nat): nat
  requires k <= |rows|
{
  if k == 0 then 0 else TotalLenUpTo(rows, k - 1) + |rows[k - 1]|
}

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |pairs_list| + 3 * TotalLenUpTo(pairs_list, |pairs_list|) + 4
{
  steps := 1;
  var a: seq<int> := [];
  var i := 0;
  while i < |pairs_list|
    invariant 0 <= i <= |pairs_list|
    invariant |a| == TotalLenUpTo(pairs_list, i)
    invariant steps == 4 * i + |a| + 1
    decreases |pairs_list| - i
  {
    ghost var lenBefore := |a|;
    a := a + pairs_list[i];
    assert |a| == lenBefore + |pairs_list[i]|;
    steps := steps + 4 + |pairs_list[i]|;
    i := i + 1;
  }
  ghost var s1 := steps;
  var count := 0;
  var idx := 0;
  while idx + 1 < |a|
    invariant 0 <= idx <= |a|
    invariant steps == s1 + 2 * idx
    decreases |a| - idx
  {
    if AbsInt(a[idx] - a[idx + 1]) >= 2 {
      count := count + 1;
    }
    idx := idx + 2;
    steps := steps + 4;
  }
  output := IntToString(count);
  steps := steps + 2;
}
