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

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires forall v :: v in a_list ==> 1 <= v <= |s|
  ensures steps <= 5 * |a_list| + 4 * |s| + 4
{
  steps := 1;
  var strLen := |s|;
  var l := seq(strLen + 1, _ => 0);
  steps := steps + 1;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant |l| == strLen + 1
    invariant steps <= 5 * idx + 2
    decreases |a_list| - idx
  {
    var v := a_list[idx];
    assert v in a_list;
    l := l[v - 1 := l[v - 1] + 1];
    l := l[strLen - v + 1 := l[strLen - v + 1] - 1];
    idx := idx + 1;
    steps := steps + 5;
  }
  var k := 0;
  var result: seq<char> := [];
  idx := 0;
  steps := steps + 2;
  while idx < strLen
    invariant 0 <= idx <= strLen
    invariant |l| == strLen + 1
    invariant steps <= 5 * |a_list| + 2 + 4 * idx + 2
    decreases strLen - idx
  {
    k := k + l[idx];
    if k % 2 == 0 {
      result := result + [s[idx]];
    } else {
      result := result + [s[strLen - idx - 1]];
    }
    idx := idx + 1;
    steps := steps + 4;
  }
  assert idx == strLen;
  assert steps <= 5 * |a_list| + 4 * strLen + 4;
  output := result;
}
