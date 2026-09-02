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

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data: seq<(int, int, int)>) returns (output: string)
  requires forall k :: 0 <= k < |data| ==> data[k].0 >= 2 && 0 <= data[k].1 < data[k].2
{
  output := "";
  var t := 0;
  while t < |data|
    invariant 0 <= t <= |data|
    decreases |data| - t
  {
    var (nn, x, y) := data[t];
    var arr: seq<(int, int)> := [];
    var i := 1;
    while i < nn
      invariant 1 <= i <= nn
      invariant i > 1 ==> |arr| >= 1
      invariant forall k :: 0 <= k < |arr| ==> arr[k].1 > 0
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
    }
    var best := arr[0];
    var j := 1;
    while j < |arr|
      invariant 1 <= j <= |arr|
      invariant best.1 > 0
      decreases |arr| - j
    {
      if arr[j].0 < best.0 || (arr[j].0 == best.0 && arr[j].1 < best.1) {
        best := arr[j];
      }
      j := j + 1;
    }
    var total := best.0;
    var step := best.1;
    var start := total - step * (nn - 1);
    var vals: seq<int> := [];
    var v := start;
    while v <= total
      invariant step > 0
      decreases total - v
    {
      vals := vals + [v];
      v := v + step;
    }
    output := output + JoinInts(vals, " ") + "\n";
    t := t + 1;
  }
}
