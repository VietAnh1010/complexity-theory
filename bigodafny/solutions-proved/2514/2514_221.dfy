// 1084_B. Kvass and the Fair Nut  (problem 2514, solution 2514_221)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = list(map(int,input().split()))
// s = n[1]
// n = n[0]
// a = list(map(int,input().split()))
//
// a = sorted(a,reverse = True)
// k = min(a)
// su = 0
// if s > sum(a):
//     print(-1)
// else:
//     for i in range(len(a)):
//         if a[i] > k:
//             su += (a[i]-k)
//             a[i] = k
//             if su >= s:
//                 break
//     if su < s:
//         k = (n*k-(s-su))//n
//         print(k)
//     else:
//         print(k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Prelude.Sort is a plain recursive function (merge sort); it carries no
// ghost step counter (prelude.dfy is off limits), so its cost is charged as
// an opaque-but-defined SortCost mirroring Sort's own split. The bound proved
// here is an honest O(k^2) -- weaker than merge sort's true O(k log k) -- so
// the row's proved complexity does not match its O(nlogn) label tightly.
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

method Solve(a: int, b: int, c_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |c_list| >= 1
  requires a >= 1
  ensures steps <= 2 * |c_list| * |c_list| + 6 * |c_list| + 10
{
  var arr := Sort(c_list, (x: int, y: int) => x > y);
  SortCostBound(|c_list|);
  var kk := MinSeq(c_list);
  var su := 0;
  var total := SumSeq(c_list);
  // MinSeq/SumSeq are recursive prelude functions over a seq; the charge
  // table costs a walk over the whole sequence, so |c_list| each.
  steps := 1 + SortCost(|c_list|) + 2 * |c_list|;
  if b > total {
    output := "-1";
    steps := steps + 1;
  } else {
    var i := 0;
    while i < |arr| && su < b
      invariant 0 <= i <= |arr|
      invariant |arr| == |c_list|
      invariant steps <= 1 + SortCost(|c_list|) + 2 * |c_list| + 2 * i
      decreases |arr| - i
    {
      if arr[i] > kk {
        su := su + (arr[i] - kk);
        arr := arr[i := kk];
      }
      i := i + 1;
      steps := steps + 2;
    }
    if su < b {
      var res := FloorDiv(a * kk - (b - su), a);
      output := IntToString(res);
      steps := steps + 2;
    } else {
      output := IntToString(kk);
      steps := steps + 1;
    }
  }
}
