// 794_794 (problem 794) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : 20000 * |data| * |data| + 8100000 * |data| + 10
//   proved class    : O(n**2)
//   agent verdict   : proves
//   reference label : O(n)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     outer loop over |data| test cases repeatedly does output := output +
//     JoinInts(...); each concat costs O(|output|), and per-test-case work
//     is bounded by a constant once n,x,y are capped at 50 per
//     description.md, so the driving cost is the O(t) repeated
//     concatenations summing to O(t^2) with t = |data|; the formal parameter
//     n is unused in the body (a decoy)
//
//   agent notes:
//     Capped nn,x,y<=50 (description.md bounds) so per-test work is O(1);
//     real driver is output:=output+JoinInts(..)+"\n" inside the outer
//     |data|-loop, each concat costing O(|output|), giving O(t^2). Bounded
//     seq-append and Join costs via small lemmas (MulMonoRight, JoinBoundBy,
//     IntToStringLen) to avoid nonlinear-arithmetic timeouts. Constants left
//     very loose (20000/8.1M) since only the class matters.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 794_794
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
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
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- arithmetic helpers used only to bound `steps` ------------------------
// Z3 does not do nonlinear arithmetic well, so every multiplication that
// involves two variables is isolated into its own tiny lemma.

lemma MulMonoRight(a: int, p: int, q: int)
  requires a >= 0 && p <= q
  ensures a * p <= a * q
{}

lemma DivLeSelf(a: int, b: int)
  requires a >= 0 && b >= 1
  ensures a / b <= a
{
  assert a == b * (a / b) + a % b;
  MulMonoRight(a / b, 1, b);
}

lemma SqStep(t: int)
  requires t >= 0
  ensures (t + 1) * (t + 1) == t * t + 2 * t + 1
{}

lemma QuadBound(t: int)
  requires t >= 0
  ensures 20000 * ((t + 1) * (t + 1)) == 20000 * t * t + 40000 * t + 20000
{
  SqStep(t);
}

// A bound on the length of `Join`, given a bound on every part's length.
lemma JoinBoundBy(parts: seq<string>, sep: string, maxLen: nat)
  requires forall k :: 0 <= k < |parts| ==> |parts[k]| <= maxLen
  ensures |Join(parts, sep)| <= |parts| * (maxLen + |sep|)
  decreases |parts|
{
  if |parts| <= 1 {
  } else {
    assert forall k :: 0 <= k < |parts[1..]| ==> |parts[1..][k]| <= maxLen;
    JoinBoundBy(parts[1..], sep, maxLen);
  }
}

// |IntToString(x)| <= 5 for any x with |x| <= bound <= 9999 (4 digits + sign).
lemma IntToStringBoundGen(x: int, bound: nat)
  requires bound <= 9999
  requires -(bound as int) <= x <= (bound as int)
  ensures |IntToString(x)| <= 5
{
  if x < 0 {
    IntToStringLen(-x);
  } else if x == 0 {
  } else {
    IntToStringLen(x);
  }
}

lemma JoinIntsBoundGen(xs: seq<int>, sep: string, bound: nat)
  requires bound <= 9999
  requires forall k :: 0 <= k < |xs| ==> -(bound as int) <= xs[k] <= (bound as int)
  ensures |JoinInts(xs, sep)| <= |xs| * (5 + |sep|)
{
  var parts := seq(|xs|, i requires 0 <= i < |xs| => IntToString(xs[i]));
  forall k | 0 <= k < |parts| ensures |parts[k]| <= 5 {
    IntToStringBoundGen(xs[k], bound);
  }
  JoinBoundBy(parts, sep, 5);
}

method Solve(n: int, data: seq<(int, int, int)>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |data| ==> data[k].0 >= 2 && 0 <= data[k].1 < data[k].2
  requires forall k :: 0 <= k < |data| ==> data[k].0 <= 50 && data[k].2 <= 50
  ensures steps <= 20000 * |data| * |data| + 8100000 * |data| + 10
{
  output := "";
  steps := 1;
  var t := 0;
  while t < |data|
    invariant 0 <= t <= |data|
    invariant |output| <= 20000 * t
    invariant steps <= 20000 * t * t + 8100000 * t + 10
    decreases |data| - t
  {
    var (nn, x, y) := data[t];
    var arr: seq<(int, int)> := [];
    var i := 1;
    ghost var isteps: nat := 0;
    while i < nn
      invariant 1 <= i <= nn
      invariant i > 1 ==> |arr| >= 1
      invariant forall k :: 0 <= k < |arr| ==> arr[k].1 > 0
      invariant forall k :: 0 <= k < |arr| ==> 1 <= arr[k].0 <= 2500 && 1 <= arr[k].1 <= 50
      invariant |arr| <= i - 1
      invariant isteps <= 100 * (i - 1)
      decreases nn - i
    {
      if (y - x) % i == 0 {
        assert i <= y - x;
        DivLeSelf(y - x, i);
        var step := (y - x) / i;
        assert step > 0;
        assert step <= y - x;
        var smol := x % step;
        if smol == 0 { smol := smol + step; }
        assert smol <= step;
        MulMonoRight(step, nn - 1, 49);
        var total := smol + step * (nn - 1);
        assert total <= step + step * 49;
        assert step + step * 49 == step * 50;
        assert step * 50 <= 50 * 50;
        var m := if y > total then y else total;
        assert 1 <= m <= 2500;
        isteps := isteps + (|arr| + 10);
        arr := arr + [(m, step)];
      } else {
        isteps := isteps + 10;
      }
      i := i + 1;
    }
    var best := arr[0];
    var j := 1;
    ghost var jsteps: nat := 0;
    while j < |arr|
      invariant 1 <= j <= |arr|
      invariant best.1 > 0
      invariant 1 <= best.0 <= 2500 && 1 <= best.1 <= 50
      invariant jsteps <= 20 * (j - 1)
      decreases |arr| - j
    {
      if arr[j].0 < best.0 || (arr[j].0 == best.0 && arr[j].1 < best.1) {
        best := arr[j];
      }
      j := j + 1;
      jsteps := jsteps + 20;
    }
    var total := best.0;
    var step := best.1;
    var start := total - step * (nn - 1);
    assert -2500 <= start <= 2500 by {
      MulMonoRight(step, nn - 1, 49);
      assert step * (nn - 1) <= step * 49;
      assert step * 49 <= 50 * 49;
    }
    var vals: seq<int> := [];
    var v := start;
    ghost var vsteps: nat := 0;
    while v <= total
      invariant step > 0
      invariant v <= total + step
      invariant |vals| <= v - start
      invariant forall k :: 0 <= k < |vals| ==> start <= vals[k] <= total
      invariant vsteps <= 3000 * |vals|
      decreases total - v
    {
      vsteps := vsteps + (|vals| + 10);
      vals := vals + [v];
      v := v + step;
    }
    assert forall k :: 0 <= k < |vals| ==> -2500 <= vals[k] <= 2500;
    assert |vals| <= v - start;
    assert v - start <= (total + step) - start;
    assert (total + step) - start == step * (nn - 1) + step;
    MulMonoRight(step, nn, 50);
    assert step * (nn - 1) + step == step * nn;
    assert step * nn <= step * 50;
    assert step * 50 <= 50 * 50;
    assert |vals| <= 2500;
    assert vsteps <= 3000 * 2500;
    var joined := JoinInts(vals, " ");
    JoinIntsBoundGen(vals, " ", 2500);
    assert |joined| <= |vals| * 6;
    assert |joined| <= 2500 * 6;

    assert isteps <= 100 * (nn - 1);
    assert isteps <= 100 * 49;
    assert |arr| <= nn - 1;
    assert |arr| <= 49;
    assert jsteps <= 20 * (|arr| - 1);
    assert jsteps <= 20 * 48;
    assert vsteps <= 3000 * 2500;

    ghost var out0 := output;
    assert |out0| <= 20000 * t;

    steps := steps + isteps + jsteps + vsteps;
    steps := steps + |joined|;
    steps := steps + |output| + |joined|;
    output := output + joined;
    steps := steps + |output| + 1;
    output := output + "\n";

    assert |output| <= 20000 * t + 15000 + 1;
    assert |output| <= 20000 * (t + 1);
    assert steps <= 20000 * t * t + 8100000 * t + 10 + (100 * 49) + (20 * 48) + (3000 * 2500) + 15000 + (20000 * t + 15000) + (20000 * t + 15000 + 1);
    assert steps <= 20000 * t * t + 40000 * t + 20000 + 8100000 * t + 8100000 + 10;
    QuadBound(t);
    assert 20000 * t * t + 40000 * t + 20000 == 20000 * ((t + 1) * (t + 1));
    assert steps <= 20000 * ((t + 1) * (t + 1)) + 8100000 * (t + 1) + 10;
    assert 20000 * ((t + 1) * (t + 1)) == 20000 * (t + 1) * (t + 1);
    assert steps <= 20000 * (t + 1) * (t + 1) + 8100000 * (t + 1) + 10;
    t := t + 1;
  }
}
