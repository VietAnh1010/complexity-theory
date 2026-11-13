// 841_A. Generous Kefa  (problem 2853, solution 2853_327)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=list(map(int,input().split()))
// s=input()
// count={}
// for val in s:	
// 	if(val not in count):
// 		count[val]=0
// 	count[val]+=1
// flag=0
// for item in count:
// 	if(count[item]>m):
// 		flag=1
// 		break
// if(flag==0):
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 16 * |s| + 3
{
  steps := 1;
  var count: map<char, int> := map[];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |count| <= i
    invariant steps == 1 + 8 * i
    decreases |s| - i
  {
    var val := s[i];
    if val !in count {
      count := count[val := 0];
    }
    count := count[val := count[val] + 1];
    i := i + 1;
    steps := steps + 8;
  }
  var flag := false;
  var ks := count.Keys;
  steps := steps + |count|;
  ghost var base := steps;
  while ks != {} && !flag
    invariant ks <= count.Keys
    invariant steps <= base + 6 * (|count| - |ks|)
    decreases |ks|
  {
    var item :| item in ks;
    if count[item] > k {
      flag := true;
    }
    ks := ks - {item};
    steps := steps + 6;
  }
  if flag {
    output := "NO";
  } else {
    output := "YES";
  }
  steps := steps + 1;
}
