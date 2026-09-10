// 1718_1166 (problem 1718) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n*m)
//   proved bound    : 20 * N1 * N1 + 20 * N2 * N2 + 20 * N1 * N2 + 20 * N1 + 20 * N2 + 30
//   proved class    : O(n**2+m**2)
//   agent verdict   : refutes
//   reference label : O(n*m)
//   prediction correct against the label: True
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     outer loop over N1 boys, inner loop over N2 girls (bounded by N2 even
//     with early break) -- classic O(n*m) matching, sort is lower-order.
//
//   agent notes:
//     SortInts on N1/N2 elements really costs Theta(N log N) per array,
//     independent of the other array's size. With N2 held at a fixed small
//     value and N1 growing, that sort cost is not O(N1*N2) -- so O(n*m) is
//     not provable as a genuine bound, only as one when both sizes grow
//     together. Charged both sorts flatly at N^2 (sound over-approx of N log
//     N) and the nested loop at 5*N1*N2+10*N1+10, giving a bound whose
//     dominant shape is n^2+m^2 (n*m is absorbed since n*m <= (n^2+m^2)/2).
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1718_1166
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// n = int(input())
// boys = list(map(int, input().split()))
// m = int(input())
// girls = list(map(int, input().split()))
// boys.sort()
// girls.sort()
// mark = [0]*m
// for i in range(n):
//     for j in range(m):
//         #print("{} {}".format(i, j))
//         if mark[j] == 0 and abs(boys[i] - girls[j]) <= 1:
//             #print("{} {}".format(i, j))
//             mark[j] = 1
//             break
// print(mark.count(1))
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulAdd(a: int, x: int, d: int)
  ensures a * (x + d) == a * x + a * d
{}

lemma ExpandS(N2: int, N1: int)
  ensures (5 * N2 + 10) * N1 == 5 * N1 * N2 + 10 * N1
{}

lemma FinalBound(N1: int, N2: int, sc: int, s: int)
  requires N1 >= 0 && N2 >= 0
  requires sc == N1 * N1 + N2 * N2 + N1 + N2 + 10
  requires s <= 5 * N1 * N2 + 10 * N1 + 10
  ensures sc + s + 10 <= 20 * N1 * N1 + 20 * N2 * N2 + 20 * N1 * N2 + 20 * N1 + 20 * N2 + 30
{}

method Solve(N1: int, list1: seq<int>, N2: int, list2: seq<int>) returns (output: string, ghost steps: nat)
  requires 0 <= N1 <= |list1|
  requires 0 <= N2 <= |list2|
  ensures steps <= 20 * N1 * N1 + 20 * N2 * N2 + 20 * N1 * N2 + 20 * N1 + 20 * N2 + 30
{
  var boys := SortInts(list1);
  var girls := SortInts(list2);
  // SortInts is a merge sort: real cost is O(N log N). Charged flatly here at
  // O(N^2) per array, a sound but loose over-approximation -- see notes.
  ghost var sortCost: nat := N1 * N1 + N2 * N2 + N1 + N2 + 10;

  var mark := seq(N2, (idx: int) => 0);
  var cnt := 0;
  var bi := 0;
  ghost var s: nat := 0;
  while bi < N1
    invariant 0 <= bi <= N1
    invariant |mark| == N2
    invariant |boys| == |list1| && |girls| == |list2|
    invariant s <= (5 * N2 + 10) * bi + 10
    decreases N1 - bi
  {
    var gj := 0;
    var matched := false;
    ghost var sinner: nat := 0;
    while gj < N2 && !matched
      invariant 0 <= gj <= N2
      invariant |mark| == N2
      invariant sinner <= 5 * gj + 5
      decreases N2 - gj
    {
      if mark[gj] == 0 && AbsInt(boys[bi] - girls[gj]) <= 1 {
        mark := mark[gj := 1];
        matched := true;
        cnt := cnt + 1;
      }
      gj := gj + 1;
      sinner := sinner + 5;
    }
    assert sinner <= 5 * N2 + 5;
    s := s + sinner + 5;
    MulAdd(5 * N2 + 10, bi, 1);
    bi := bi + 1;
  }
  ExpandS(N2, N1);
  assert s <= 5 * N1 * N2 + 10 * N1 + 10;
  FinalBound(N1, N2, sortCost, s);

  output := IntToString(cnt);
  steps := sortCost + s + 10;
}
