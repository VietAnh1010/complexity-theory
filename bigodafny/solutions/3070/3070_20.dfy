// 426_A. Sereja and Mugs  (problem 3070, solution 3070_20)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, s = map(int, input().split())
// a = [int(i) for i in input().split()]
// summa = 0
// for i in a:
//     summa += i
// summa -= max(a)
// if s < summa:
//     print('NO')
// else:
//     print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string)
{
  if |a_list| == 0 {
    output := "YES";
    return;
  }
  var summa := SumSeq(a_list) - MaxSeq(a_list);
  if m < summa {
    output := "NO";
  } else {
    output := "YES";
  }
}
