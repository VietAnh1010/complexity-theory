// 879_A. Borya's Diagnosis  (problem 827, solution 827_148)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = [[0,0] for i in range(n)]
// 
// for i in range(n):
//     arr[i][0] , arr[i][1] = map(int , input().split())
// 
// # arr.sort(key = lambda x: x[1])
// dates = [arr[0][0]]
// 
// for i,j in arr[1:]:
//     while i<=dates[-1] : i += j
//     dates.append(i)
// 
// 
// print(dates[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Constraints from the source problem (879_A, fetched this session from
// .cache/time_complexity_test_set.jsonl): 1 <= n <= 1000, and each doctor's
// (s_i, d_i) satisfies 1 <= s_i, d_i <= 1000. That fixed value cap (not
// scaling with n) is what makes the total inner-loop work O(n**2) rather
// than unbounded: `last` grows by at most 1000 per outer step, so each
// inner loop runs at most O(n) times, over n outer steps.

lemma SqMono(a: int, b: int)
  requires 0 <= a <= b
  ensures a * a <= b * b
{
  assert (b - a) * (b + a) == b * b - a * a;
  assert (b - a) * (b + a) >= 0;
}

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires |pairs| >= 1
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k].0 <= 1000 && 1 <= pairs[k].1 <= 1000
  ensures steps <= 10000 * |pairs| * |pairs| + 50000 * |pairs| + 600
{
  steps := 1;
  var last := pairs[0].0;
  var idx := 1;
  while idx < |pairs|
    invariant 1 <= idx <= |pairs|
    invariant 1 <= last <= 5000 * idx + 5000
    invariant steps <= 10000 * idx * idx + 50000 * idx + 500
    decreases |pairs| - idx
  {
    var idxOld := idx;
    var s0 := steps;
    var last0 := last;
    var i := pairs[idx].0;
    var j := pairs[idx].1;
    var i0 := i;
    steps := steps + 4;
    while i <= last
      invariant i0 <= i
      invariant last == last0
      invariant steps <= s0 + 4 + 2 * (i - i0)
      invariant i <= last0 + j || i <= 1000
      decreases last - i
    {
      i := i + j;
      steps := steps + 2;
    }
    // Whether the loop ran 0 or more times, i is bounded: either the guard
    // fired on the final iteration (i <= last0 + j), or it never fired and
    // i == i0 <= 1000 (problem's own value cap, fetched into the requires
    // clause above). Either way i <= last0 + j + 1000.
    assert i <= last0 + j + 1000;
    last := i;
    idx := idx + 1;
    steps := steps + 2;
    assert steps <= s0 + 2 * last0 + 2 * j + 2006;
    assert s0 <= 10000 * idxOld * idxOld + 50000 * idxOld + 500;
    assert last0 <= 5000 * idxOld + 5000;
    assert idx == idxOld + 1;
    assert 10000 * idx * idx + 50000 * idx + 500
        == 10000 * idxOld * idxOld + 70000 * idxOld + 60500;
  }
  SqMono(idx, |pairs|);
  output := IntToString(last) + "\n";
}
