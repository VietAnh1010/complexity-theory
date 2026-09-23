// 416_A. Guess a number!  (problem 1878, solution 1878_72)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = []
// less = []
// grt = []
//
// for i in range(n):
//     l = [x for x in input().split()]
//
//     if l[2] == 'N':
//         l[2] = 'Y'
//         if l[0] == '>=': l[0] = '<'
//         elif l[0] == '>': l[0] = '<='
//         elif l[0] == '<': l[0] = '>='
//         else: l[0] = '>'
//
//     if (l[0] == "<" or l[0] == "<="):
//         less.append(int(l[1]))
//         if l[0] == "<":
//             less[-1] -= 1
//
//     elif (l[0] == ">" or l[0] == ">="):
//         grt.append(int(l[1]))
//         if l[0] == ">":
//             grt[-1] += 1
//
// ##    print(less, grt)
//
// less.sort()
// grt.sort()
//
// if len(less) > 0 and len(grt) > 0:
//     v1 = less[0]
//     v2 = grt[-1]
//
//     if v1 >= v2:
//         print(v2)
//     else:
//         print("Impossible")
// elif len(less) == 0 and len(grt) > 0:
//     print(grt[-1])
// elif len(grt) == 0 and len(less) > 0:
//     print(less[0])
// elif len(less) == 0 and len(grt) == 0:
//     print("Impossible")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulMonoLeft(p: nat, q: nat, x: nat)
  requires p <= q
  ensures p * x <= q * x
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

lemma TwoSortBound(a: nat, b: nat, N: nat)
  requires a + b <= N
  ensures SortCost(a) + SortCost(b) <= 2 * N * (CeilLog2(N) + 1) + 2
{
  SortCostTreeBound(a);
  SortCostTreeBound(b);
  CeilLog2Monotone(a, N);
  CeilLog2Monotone(b, N);
  var L := CeilLog2(N) + 1;
  MulMonoRight(2 * a, CeilLog2(a) + 1, L);
  MulMonoRight(2 * b, CeilLog2(b) + 1, L);
  var s := a + b;
  MulDistrib(2 * a, 2 * b, 2 * s, L);
  MulMonoLeft(2 * s, 2 * N, L);
}

method Solve(N: int, queries: seq<(string, int, string)>) returns (output: string, ghost steps: nat)
  requires N >= 0
  requires |queries| >= N
  ensures steps <= 2 * N * (CeilLog2(N) + 1) + 6 * N + 15
{
  steps := 1;
  var less: seq<int> := [];
  var grt: seq<int> := [];
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |less| + |grt| <= i
    invariant steps <= 6 * i + 1
    decreases N - i
  {
    var a := queries[i].0;
    var k := queries[i].1;
    var c := queries[i].2;
    if c == "N" {
      c := "Y";
      if a == ">=" { a := "<"; }
      else if a == ">" { a := "<="; }
      else if a == "<" { a := ">="; }
      else { a := ">"; }
    }
    if a == "<" || a == "<=" {
      var val := k;
      if a == "<" { val := val - 1; }
      less := less + [val];
    } else if a == ">" || a == ">=" {
      var val := k;
      if a == ">" { val := val + 1; }
      grt := grt + [val];
    }
    i := i + 1;
    steps := steps + 6;
  }
  TwoSortBound(|less|, |grt|, N);
  var lessSorted := SortInts(less);
  var grtSorted := SortInts(grt);
  steps := steps + SortCost(|less|) + SortCost(|grt|) + 2;
  if |lessSorted| > 0 && |grtSorted| > 0 {
    var v1 := lessSorted[0];
    var v2 := grtSorted[|grtSorted| - 1];
    output := if v1 >= v2 then IntToString(v2) else "Impossible";
  } else if |lessSorted| == 0 && |grtSorted| > 0 {
    output := IntToString(grtSorted[|grtSorted| - 1]);
  } else if |grtSorted| == 0 && |lessSorted| > 0 {
    output := IntToString(lessSorted[0]);
  } else {
    output := "Impossible";
  }
  steps := steps + 2;
}
