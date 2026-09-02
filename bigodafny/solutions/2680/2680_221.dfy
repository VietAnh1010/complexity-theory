// 546_C. Soldier and Cards  (problem 2680, solution 2680_221)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// a = a[1:]
// b = [int(x) for x in input().split()]
// b = b[1:]
// k = 0
// while len(a) > 0 and len(b) > 0 and k <= 10 ** 3:
// 	if a[0] > b[0] and (not(a[0] == 0 and b[0] == 9) and not(a[0] == 9 and b[0] == 0)):
// 		a.append(b[0])
// 		a.append(a[0])
// 		a.pop(0)
// 		b.pop(0)
// 		k += 1
// 	else:
// 		b.append(a[0])
// 		b.append(b[0])
// 		a.pop(0)
// 		b.pop(0)
// 		k += 1
// if len(a) != 0 and len(b) != 0:
// 	print(-1)
// elif len(a) > 0:
// 	print(k, 1)
// else:
// 	print(k, 2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, list1: seq<int>, list2: seq<int>) returns (output: string)
{
  var a := list1;
  var b := list2;
  var k := 0;
  while |a| > 0 && |b| > 0 && k <= 1000
    decreases 1001 - k
  {
    var a0 := a[0];
    var b0 := b[0];
    if a0 > b0 && !(a0 == 0 && b0 == 9) && !(a0 == 9 && b0 == 0) {
      a := a[1..] + [b0, a0];
      b := b[1..];
    } else {
      b := b[1..] + [a0, b0];
      a := a[1..];
    }
    k := k + 1;
  }
  if |a| != 0 && |b| != 0 {
    output := "-1";
  } else if |a| > 0 {
    output := JoinInts([k, 1], " ");
  } else {
    output := JoinInts([k, 2], " ");
  }
}
