// 437_B. The Child and Set  (problem 1827, solution 1827_66)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s,l=map(int,input().split())
// list1=[]
// for i in range(1,l+1):
//     list1.append((i&-i,i))
//     
// list1.sort(reverse=True)
// ll=[]
// for i in range(l):
//     if(list1[i][0]<=s):
//         ll.append(list1[i][1])
//         s-=list1[i][0]
//         
// if(s==0):
//     print(len(ll))
//     print(*ll)
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Lowbit(v: int): int
  requires v >= 1
  decreases v
{
  if v % 2 == 1 then 1 else 2 * Lowbit(v / 2)
}

method Solve(a: int, b: int) returns (output: string)
{
  var s := a;
  var l := b;
  var list1: seq<(int, int)> := [];
  var i := 1;
  while i <= l
    invariant 1 <= i
    invariant l >= 1 ==> i <= l + 1
    invariant |list1| == i - 1
    decreases l - i
  {
    list1 := list1 + [(Lowbit(i), i)];
    i := i + 1;
  }
  var sorted := Sort(list1, (p: (int, int), q: (int, int)) =>
    if p.0 != q.0 then p.0 > q.0 else p.1 > q.1);
  // l < 1 leaves list1 empty and the next loop never runs.
  assert l >= 1 ==> |sorted| == l;
  var ll: seq<int> := [];
  var k := 0;
  while k < l
    invariant 0 <= k
    invariant l >= 1 ==> |sorted| == l
    decreases l - k
  {
    if sorted[k].0 <= s {
      ll := ll + [sorted[k].1];
      s := s - sorted[k].0;
    }
    k := k + 1;
  }
  if s == 0 {
    output := IntToString(|ll|) + "\n" + JoinInts(ll, " ");
  } else {
    output := IntToString(-1);
  }
}
