// 525_B. Pasha and String  (problem 380, solution 380_19)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = list(input())
// n = len(s)
// m = int(input())
// a = list(map(int,input().split()))
// l = [0]*(n+1)
// for i in a:
// 	l[i-1]+=1
// 	l[n-i+1]-=1
// k = 0
// l2 = []
// for i in range(n):
// 	k += l[i]
// 	if k%2==0:
// 		l2.append(s[i])
// 	else:
// 		l2.append(s[n-i-1])
// print("".join(l2)) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
  requires forall v :: v in a_list ==> 1 <= v <= |s|
{
  var strLen := |s|;
  var l := new int[strLen + 1];
  var idx := 0;
  while idx < strLen + 1
    decreases strLen + 1 - idx
  {
    l[idx] := 0;
    idx := idx + 1;
  }
  idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    decreases |a_list| - idx
  {
    var v := a_list[idx];
    assert v in a_list;
    l[v - 1] := l[v - 1] + 1;
    l[strLen - v + 1] := l[strLen - v + 1] - 1;
    idx := idx + 1;
  }
  var k := 0;
  var result: seq<char> := [];
  idx := 0;
  while idx < strLen
    decreases strLen - idx
  {
    k := k + l[idx];
    if k % 2 == 0 {
      result := result + [s[idx]];
    } else {
      result := result + [s[strLen - idx - 1]];
    }
    idx := idx + 1;
  }
  output := result;
}
