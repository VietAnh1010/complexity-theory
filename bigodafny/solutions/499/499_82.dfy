// 1206_B. Make Product Equal One  (problem 499, solution 499_82)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// a.sort()
// ans=0
// for i in range(0,n-1,2):
//     ans+=min(abs(-1-a[i+1])+abs(-1-a[i]),abs(1-a[i+1])+abs(1-a[i]))
// if (n%2==1): ans+=abs(1-a[n-1])
// print(ans)
//     
//     
//     
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 0
  requires |a_list| == n
{
  var a := SortInts(a_list);
  var ans := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i
    decreases n - 1 - i
  {
    var opt1 := Abs82(-1 - a[i+1]) + Abs82(-1 - a[i]);
    var opt2 := Abs82(1 - a[i+1]) + Abs82(1 - a[i]);
    ans := ans + (if opt1 < opt2 then opt1 else opt2);
    i := i + 2;
  }
  if n % 2 == 1 {
    ans := ans + Abs82(1 - a[n-1]);
  }
  output := IntToString(ans) + "\n";
}

function Abs82(x: int): int
{
  if x < 0 then -x else x
}
