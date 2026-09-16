// 1234_B1. Social Network (easy version)  (problem 64, solution 64_1063)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import deque
// n,k=map(int,input().split())
// inp=list(map(int,input().split()))
// listt=deque()
// dictt={}
// for i in inp:
// 	dictt[i]=False
// for i in inp:
// 	if len(listt)<k:
// 		if  dictt[i]==False:
// 			listt.appendleft(i)
// 			# listt=[i]+listt
// 			dictt[i]=True
// 	if len(listt)==k:
// 		if dictt[i]==False:
// 			dictt[i]=True
// 			dictt[listt[-1]]=False
// 			# listt=[i]+listt
// 			listt.appendleft(i)
// 			# listt=listt[:-1]
// 			listt.pop()
// 	# print(listt)
// 	# print(dictt)
// 
// print(len(listt))
// print(*listt)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, ratings: seq<int>) returns (output: string)
{
  var listt: seq<int> := [];
  var present: set<int> := {};
  var idx := 0;
  while idx < |ratings|
    decreases |ratings| - idx
  {
    var v := ratings[idx];
    if |listt| < k {
      if v !in present {
        listt := [v] + listt;
        present := present + {v};
      }
    }
    if |listt| == k {
      if v !in present {
        present := present - {listt[|listt| - 1]};
        present := present + {v};
        listt := [v] + listt[..|listt| - 1];
      }
    }
    idx := idx + 1;
  }
  output := IntToString(|listt|) + "\n" + JoinInts(listt, " ");
}
