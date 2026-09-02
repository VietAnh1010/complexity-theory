// 525_B. Pasha and String  (problem 380, solution 380_112)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = list(input())
// m = int(input())
// n=len(s)
// lis = sorted(map(int,input().split()))
// has=[0]*(n+3)
// for i in range(m):
//     a=lis[i]
//     has[a-1]+=1
// for i in range(1,n+2):
//     has[i]+=has[i-1]       
// for i in range(n//2):
//     if has[i]%2:
//         s[i],s[n-i-1]=s[n-i-1],s[i]
// print(''.join(s))               
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
{
  var m := n;
  var strLen := |s|;
  var aSorted := SortInts(a_list);
  var has := new int[strLen + 3];
  var k := 0;
  while k < strLen + 3
    decreases strLen + 3 - k
  {
    has[k] := 0;
    k := k + 1;
  }
  var i := 0;
  while i < m
    decreases m - i
  {
    var a := aSorted[i];
    has[a - 1] := has[a - 1] + 1;
    i := i + 1;
  }
  i := 1;
  while i < strLen + 2
    decreases strLen + 2 - i
  {
    has[i] := has[i] + has[i - 1];
    i := i + 1;
  }
  var arr := new char[strLen];
  i := 0;
  while i < strLen
    decreases strLen - i
  {
    arr[i] := s[i];
    i := i + 1;
  }
  i := 0;
  while i < strLen / 2
    decreases strLen / 2 - i
  {
    if has[i] % 2 == 1 {
      var tmp := arr[i];
      arr[i] := arr[strLen - i - 1];
      arr[strLen - i - 1] := tmp;
    }
    i := i + 1;
  }
  output := arr[..];
}
