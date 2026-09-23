// 1409_C. Yet Another Array Restoration  (problem 794, solution 794_794)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
//
// def solve():
//     n,x,y=map(int,input().split())
//     arr = []
//     for i in range(1,n):
//         if (y-x)%i==0:
//             step = (y-x)//i
//             smol = x%step
//             if smol == 0:
//                 smol+=step
//             total = smol+step*(n-1)
//             arr.append((max(total,y),step))
//
//     total,step = min(arr)
//     print(*range(total-step*(n-1),total+1,step))
//
// if __name__=="__main__":
//     for _ in range(int(input())):
//         solve()
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

// Each test's own trip count is the per-test value `nn` (data[t].0), not the
// length of anything read as an array -- Python never reads an nn-length
// sequence here, it only loops range(1,nn). Per COMPLEXITY.md's value-vs-size
// convention that value counts as its own parameter, so the bound is stated
// against the sum of the nn's, not against |data| alone.
ghost function SumNN(data: seq<(int, int, int)>, upto: nat): nat
  requires upto <= |data|
  requires forall k :: 0 <= k < |data| ==> data[k].0 >= 0
  decreases upto
{
  if upto == 0 then 0 else SumNN(data, upto - 1) + data[upto - 1].0
}

lemma SumNNSnoc(data: seq<(int, int, int)>, upto: nat)
  requires upto < |data|
  requires forall k :: 0 <= k < |data| ==> data[k].0 >= 0
  ensures SumNN(data, upto + 1) == SumNN(data, upto) + data[upto].0
{
}

method Solve(n: int, data: seq<(int, int, int)>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |data| ==> data[k].0 >= 2 && 0 <= data[k].1 < data[k].2
  ensures steps <= 30 * |data| + 30 * SumNN(data, |data|) + 3
{
  steps := 1;
  output := "";
  var t := 0;
  while t < |data|
    invariant 0 <= t <= |data|
    invariant steps <= 1 + 30 * t + 30 * SumNN(data, t)
    decreases |data| - t
  {
    SumNNSnoc(data, t);
    var (nn, x, y) := data[t];
    var arr: seq<(int, int)> := [];
    var i := 1;
    ghost var arrSteps := steps;
    while i < nn
      invariant 1 <= i <= nn
      invariant i > 1 ==> |arr| >= 1
      invariant |arr| <= i - 1
      invariant forall k :: 0 <= k < |arr| ==> arr[k].1 > 0
      invariant steps <= arrSteps + 6 * (i - 1)
      decreases nn - i
    {
      if (y - x) % i == 0 {
        assert i <= y - x;
        var step := (y - x) / i;
        assert step > 0;
        var smol := x % step;
        if smol == 0 { smol := smol + step; }
        var total := smol + step * (nn - 1);
        var m := if y > total then y else total;
        arr := arr + [(m, step)];
      }
      i := i + 1;
      steps := steps + 6;
    }
    var best := arr[0];
    var j := 1;
    ghost var bestSteps := steps;
    while j < |arr|
      invariant 1 <= j <= |arr|
      invariant best.1 > 0
      invariant steps <= bestSteps + 3 * (j - 1)
      decreases |arr| - j
    {
      if arr[j].0 < best.0 || (arr[j].0 == best.0 && arr[j].1 < best.1) {
        best := arr[j];
      }
      j := j + 1;
      steps := steps + 3;
    }
    var total := best.0;
    var step := best.1;
    var start := total - step * (nn - 1);
    var vals: seq<int> := [];
    var v := start;
    ghost var valsSteps := steps;
    ghost var vcount: nat := 0;
    while v <= total
      invariant step > 0
      invariant v == start + vcount * step
      invariant vcount <= nn
      invariant |vals| == vcount
      invariant steps <= valsSteps + 2 * vcount
      decreases total - v
    {
      vals := vals + [v];
      v := v + step;
      vcount := vcount + 1;
      steps := steps + 2;
      assert start + (nn - 1) * step == total;
      assert vcount <= nn;
    }
    // |arr| <= nn - 1 (one slot appended per outer-loop-1 iteration) and the
    // range in loop 3 walks at most nn steps (Python's own invariant: the
    // chosen arithmetic progression has exactly nn terms).
    assert |arr| <= nn - 1;
    assert |vals| == vcount;
    assert |vals| <= nn;
    steps := steps + JoinIntsCost(vals) + 12;
    output := output + JoinInts(vals, " ") + "\n";
    assert steps <= arrSteps + 6 * (nn - 1) + 3 * (nn - 2) + 2 * nn + nn + 12;
    assert steps <= 1 + 30 * t + 30 * SumNN(data, t) + 30 * nn;
    SumNNSnoc(data, t);
    assert SumNN(data, t + 1) == SumNN(data, t) + nn;
    t := t + 1;
  }
}

// Placeholder cost accessor: Join over int-valued parts is charged |parts|
// under the IntToString/Join digit-string exception, never the sum of digit
// lengths, so the whole `vals` sequence -- itself bounded by nn terms -- costs
// |vals|. Kept as an opaque nat rather than inlined so the final steps bound
// stays linear in the charge, matching the exception's intent.
ghost function JoinIntsCost(vals: seq<int>): nat { |vals| }
