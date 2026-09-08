// 1105_B. Zuhair and Strings  (problem 2231, solution 2231_194)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=input().split()
// n=int(n)
// k=int(k)
// s=input()
// 
// 
// arr=[]
// f=s[0]
// z=''
// for i in range (len(s)):
//     if s[i]==f:
//         z=z+s[i]
//     else:
//         f=s[i]
//         arr.append(z)
//         z=f
// arr.append(z)
// arr
// 
// arr.sort()
// 
// f=arr[0][0]
// c=0
// i=0
// q=[]
// while i<len(arr):
//     if f in arr[i]:
//         c=c+int(len(arr[i])/k)
//     else:
//         q.append(c)
//         c=0
//         
//         f=arr[i][0]
//         i=i-1
//         pass
//     i=i+1
// q.append(c)
// 
// print(max(q))
//         
//         
//         
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, string_: string) returns (output: string)
  requires b >= 1
  requires |string_| >= 1
{
  var k := b;
  var s := string_;
  var arr: seq<string> := [];
  if |s| > 0 {
    var f := s[0];
    var z: string := "";
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant i == 0 ==> f == s[0]
      invariant i >= 1 ==> |z| >= 1
      invariant forall x :: x in arr ==> |x| >= 1
      decreases |s| - i
    {
      if s[i] == f {
        z := z + [s[i]];
      } else {
        f := s[i];
        arr := arr + [z];
        z := [s[i]];
      }
      i := i + 1;
    }
    arr := arr + [z];
  }
  assert |arr| >= 1;
  SortStringsKeepsElems(arr);
  var sortedArr := SortStrings(arr);
  assert forall x :: x in sortedArr ==> |x| >= 1;
  arr := sortedArr;
  var curChar := arr[0][0];
  var c := 0;
  var q: seq<int> := [];
  var idx := 0;
  while idx < |arr|
    invariant 0 <= idx <= |arr|
    invariant forall x :: x in arr ==> |x| >= 1
    decreases |arr| - idx
  {
    if arr[idx][0] == curChar {
      c := c + FloorDiv(|arr[idx]|, k);
    } else {
      q := q + [c];
      c := FloorDiv(|arr[idx]|, k);
      curChar := arr[idx][0];
    }
    idx := idx + 1;
  }
  q := q + [c];
  output := IntToString(MaxSeq(q));
}
