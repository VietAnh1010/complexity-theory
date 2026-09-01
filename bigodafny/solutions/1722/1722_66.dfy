// 887_B. Cubes for Masha  (problem 1722, solution 1722_66)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = []
// a += [list(input())]
// if (n > 1):
//     a += [list(input())]
// if (n > 2):
//     a += [list(input())]
// i = 1
// while (i < 1000):
//     s = list(str(i))
//     if (n == 1):
//         if (s[0] in a[0]):
//             i += 1
//             continue
//     if (n == 2):
//         if (len(s) == 1 and (s[0] in a[0] or s[0] in a[1])):
//             i += 1
//             continue
//         if (len(s) == 2 and (
//             (s[0] in a[0] and s[1] in a[1]) or
//             (s[0] in a[1] and s[1] in a[0]))):
//             i += 1
//             continue
//     if (n == 3):
//         if (len(s) == 1 and (s[0] in a[0] or s[0] in a[1] or s[0] in a[2])):
//             i += 1
//             continue
//         if (len(s) == 2 and (
//             (s[0] in a[0] and s[1] in a[1]) or
//             (s[0] in a[0] and s[1] in a[2]) or
//             (s[0] in a[1] and s[1] in a[0]) or
//             (s[0] in a[1] and s[1] in a[2]) or
//             (s[0] in a[2] and s[1] in a[0]) or
//             (s[0] in a[2] and s[1] in a[1]))):
//             i += 1
//             continue
//         if (len(s) == 3 and (
//             (s[0] in a[0] and s[1] in a[1] and s[2] in a[2]) or
//             (s[0] in a[0] and s[1] in a[2] and s[2] in a[1]) or
//             (s[0] in a[1] and s[1] in a[0] and s[2] in a[2]) or
//             (s[0] in a[1] and s[1] in a[2] and s[2] in a[0]) or
//             (s[0] in a[2] and s[1] in a[0] and s[2] in a[1]) or
//             (s[0] in a[2] and s[1] in a[1] and s[2] in a[0])
//             )):
//             i += 1
//             continue
//     print (i-1)
//     break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  var i := 1;
  var ans := 0;
  var done := false;
  while i < 1000 && !done
    decreases if done then 0 else 1000 - i
  {
    var s := Digits1722_66(i);
    var skip := false;
    if n == 1 {
      if ContainsInt1722_66(lists[0], s[0]) { skip := true; }
    } else if n == 2 {
      if |s| == 1 {
        if ContainsInt1722_66(lists[0], s[0]) || ContainsInt1722_66(lists[1], s[0]) { skip := true; }
      } else if |s| == 2 {
        if (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[1], s[1])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[0], s[1])) {
          skip := true;
        }
      }
    } else if n == 3 {
      if |s| == 1 {
        if ContainsInt1722_66(lists[0], s[0]) || ContainsInt1722_66(lists[1], s[0]) || ContainsInt1722_66(lists[2], s[0]) { skip := true; }
      } else if |s| == 2 {
        if (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[1], s[1])) ||
           (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[2], s[1])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[0], s[1])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[2], s[1])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[0], s[1])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[1], s[1])) {
          skip := true;
        }
      } else if |s| == 3 {
        if (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[1], s[1]) && ContainsInt1722_66(lists[2], s[2])) ||
           (ContainsInt1722_66(lists[0], s[0]) && ContainsInt1722_66(lists[2], s[1]) && ContainsInt1722_66(lists[1], s[2])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[0], s[1]) && ContainsInt1722_66(lists[2], s[2])) ||
           (ContainsInt1722_66(lists[1], s[0]) && ContainsInt1722_66(lists[2], s[1]) && ContainsInt1722_66(lists[0], s[2])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[0], s[1]) && ContainsInt1722_66(lists[1], s[2])) ||
           (ContainsInt1722_66(lists[2], s[0]) && ContainsInt1722_66(lists[1], s[1]) && ContainsInt1722_66(lists[0], s[2])) {
          skip := true;
        }
      }
    }
    if skip {
      i := i + 1;
    } else {
      ans := i - 1;
      done := true;
    }
  }
  output := IntToString(ans);
}

function Digits1722_66(i: int): seq<int>
{
  if i < 10 then [i]
  else if i < 100 then [i / 10, i % 10]
  else [i / 100, (i / 10) % 10, i % 10]
}

function ContainsInt1722_66(xs: seq<int>, v: int): bool
{
  exists k :: 0 <= k < |xs| && xs[k] == v
}
