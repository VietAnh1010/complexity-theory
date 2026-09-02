// 546_C. Soldier and Cards  (problem 2680, solution 2680_65)
// time complexity: O(n**2+m**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import deque
// n = int(input())
// a = deque([int(i) for i in input().split()[1:]])
// b = deque([int(i) for i in input().split()[1:]])
// mark = set()
// ans = 0
// while a and b:
//     if str(a)+" "+str(b) in mark:
//         print(-1)
//         exit()
//     mark.add(str(a)+" "+str(b))
//     ans += 1
//     aa = a.popleft()
//     bb = b.popleft()
//     if aa > bb:
//         a.append(bb)
//         a.append(aa)
//     else:
//         b.append(aa)
//         b.append(bb)
// if a:
//     print(ans,1)
// else:
//     print(ans,2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, list1: seq<int>, list2: seq<int>) returns (output: string)
  decreases *
{
  var a := list1;
  var b := list2;
  var mark: set<(seq<int>, seq<int>)> := {};
  var ans := 0;
  var out := "";
  var found := false;
  while |a| > 0 && |b| > 0 && !found
    decreases *
  {
    if (a, b) in mark {
      out := "-1";
      found := true;
    } else {
      mark := mark + {(a, b)};
      ans := ans + 1;
      var aa := a[0];
      var bb := b[0];
      a := a[1..];
      b := b[1..];
      if aa > bb {
        a := a + [bb, aa];
      } else {
        b := b + [aa, bb];
      }
    }
  }
  if !found {
    if |a| > 0 {
      out := JoinInts([ans, 1], " ");
    } else {
      out := JoinInts([ans, 2], " ");
    }
  }
  output := out;
}
