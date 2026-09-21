// 998_A. Balloons  (problem 2225, solution 2225_154)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// z=sorted(l)
// for i in range(n):
//   if(l[i]==z[0]):
//     mi=i
// if(n>2):
//   print(1)
//   print(mi+1)
// else:
//   if(n==2):
//     if(l[0]==l[1]):
//       print(-1)
//     else:
//       print(1)
//       print(1)
//   else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// SortInts is a plain recursive function in prelude.dfy (off limits, so no
// ghost step counter can be attached there). Its cost is charged as an
// opaque-but-defined function SortCost, whose recursion mirrors Sort's own
// split. SortCostBound proves a quadratic bound -- looser than the true
// O(k log k) (proved elsewhere in this corpus, solutions-proved/nlogn/, via
// a CeilLog2 recursion-tree argument): relation looser-slack.
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

lemma SquareSplit(k: nat, L: nat)
  requires 2 * L <= k <= 2 * L + 1
  ensures 2 * L * L + 2 * (k - L) * (k - L) <= k * k + 1
{
  var d := k - 2 * L;
  assert d == 0 || d == 1;
  assert k - L == L + d;
  assert 2 * L * L + 2 * (k - L) * (k - L) == 4 * L * L + 4 * L * d + 2 * d * d;
  assert k == 2 * L + d;
  assert k * k == 4 * L * L + 4 * L * d + d * d;
  assert d * d <= 1;
}

lemma QuadTail(k: nat)
  requires k >= 2
  ensures k * k + k + 3 <= 2 * k * k + 1
{
  assert (k - 2) * (k + 1) >= 0;
}

lemma SortCostBound(k: nat)
  ensures SortCost(k) <= 2 * k * k + 1
  decreases k
{
  if k <= 1 {
  } else {
    var L := k / 2;
    var R := k - L;
    SortCostBound(L);
    SortCostBound(R);
    SquareSplit(k, L);
    assert SortCost(k) == SortCost(L) + SortCost(R) + k;
    assert SortCost(L) + SortCost(R) + k <= (2 * L * L + 1) + (2 * R * R + 1) + k;
    assert (2 * L * L + 1) + (2 * R * R + 1) + k == 2 * L * L + 2 * R * R + k + 2;
    assert 2 * L * L + 2 * R * R + k + 2 <= (k * k + 1) + k + 2;
    QuadTail(k);
  }
}

method Solve(n: int, dimensions: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |dimensions| == n
  ensures steps <= 2 * n * n + 2 * n + 6
{
  var l := dimensions;
  SortCostBound(n);
  var z := SortInts(l);
  steps := 1 + SortCost(n);
  var minVal := z[0];
  var mi := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + SortCost(n) + 2 * i
  {
    if l[i] == minVal {
      mi := i;
    }
    i := i + 1;
    steps := steps + 2;
  }
  if n > 2 {
    output := "1\n" + IntToString(mi + 1) + "\n";
  } else if n == 2 {
    if l[0] == l[1] {
      output := "-1\n";
    } else {
      output := "1\n1\n";
    }
  } else {
    output := "-1\n";
  }
  steps := steps + 3;
}
