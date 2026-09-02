// 489_B. BerSU Ball  (problem 1718, solution 1718_1166)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
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
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N1: int, list1: seq<int>, N2: int, list2: seq<int>) returns (output: string)
{
  var boys := SortInts(list1);
  var girls := SortInts(list2);
  var mark := seq(N2, (idx: int) => 0);
  var cnt := 0;
  var bi := 0;
  while bi < N1
    decreases N1 - bi
  {
    var gj := 0;
    var matched := false;
    while gj < N2 && !matched
      decreases N2 - gj
    {
      if mark[gj] == 0 && AbsInt(boys[bi] - girls[gj]) <= 1 {
        mark := mark[gj := 1];
        matched := true;
        cnt := cnt + 1;
      }
      gj := gj + 1;
    }
    bi := bi + 1;
  }
  output := IntToString(cnt);
}
