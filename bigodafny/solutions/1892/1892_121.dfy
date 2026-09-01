// 1149_A. Prefix Sum Primes  (problem 1892, solution 1892_121)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// flag1=0
// flag2=0
// for i in range(n):
// 	if l[i]==2:
// 		flag1=1
// 		break
// for i in range(n):
// 	if l[i]==1:
// 		flag2=1
// 		break
// if flag1==0 or flag2==0:
// 	print(*l)
// else:
// 	print(2,1,end=' ')
// 	l.remove(2)
// 	l.remove(1)
// 	l.sort(reverse=True)
// 	print(*l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function RemoveFirst(l: seq<int>, x: int): seq<int>
  decreases |l|
{
  if |l| == 0 then []
  else if l[0] == x then l[1..]
  else [l[0]] + RemoveFirst(l[1..], x)
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var l := a_list;
  var flag1 := false;
  var flag2 := false;
  var i := 0;
  while i < n && !flag1
    decreases !flag1, n - i
  {
    if l[i] == 2 { flag1 := true; }
    i := i + 1;
  }
  i := 0;
  while i < n && !flag2
    decreases !flag2, n - i
  {
    if l[i] == 1 { flag2 := true; }
    i := i + 1;
  }
  if !flag1 || !flag2 {
    output := JoinInts(l, " ");
  } else {
    var rest := RemoveFirst(l, 2);
    rest := RemoveFirst(rest, 1);
    var descending := Sort(rest, (x: int, y: int) => x > y);
    output := "2 1 " + JoinInts(descending, " ");
  }
}
