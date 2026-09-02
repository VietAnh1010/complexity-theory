// 999_C. Alphabetic Removals  (problem 2725, solution 2725_140)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// a=list(input().strip())
// count=[0]*26
// aaa=ord('a')
// for i in a:
//     count[ord(i)-aaa]+=1
// deletables=-1
// for i in range(26):
//     if(count[i]>=k):
//         count=k
//         ele=i
//         break
//     deletables=i
//     k-=count[i]
// ans=""
// for i in a:
//     if(ord(i)-aaa<=deletables):
//         continue
//     if(chr(ele+aaa)==i):
//         if(count>0):
//             count-=1
//         else:
//             ans+=i
//     else:
//         ans+=i
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string)
{
  var count := new int[26];
  var z := 0;
  while z < 26
    invariant 0 <= z <= 26
  {
    count[z] := 0;
    z := z + 1;
  }
  var idx := 0;
  while idx < |s|
    invariant 0 <= idx <= |s|
  {
    var pos := (s[idx] as int) - ('a' as int);
    if 0 <= pos < 26 {
      count[pos] := count[pos] + 1;
    }
    idx := idx + 1;
  }
  var deletables := -1;
  var ele := 0;
  var kk := k;
  var countRemaining := 0;
  var found := false;
  var j := 0;
  while j < 26 && !found
    invariant 0 <= j <= 26
  {
    if count[j] >= kk {
      countRemaining := kk;
      ele := j;
      found := true;
    } else {
      deletables := j;
      kk := kk - count[j];
    }
    j := j + 1;
  }
  var buf := new char[|s|];
  var w := 0;
  var cnt := countRemaining;
  var i2 := 0;
  while i2 < |s|
    invariant 0 <= i2 <= |s|
    invariant 0 <= w <= i2
  {
    var pos := (s[i2] as int) - ('a' as int);
    if pos <= deletables {
      // deleted tier: skip entirely
    } else if pos == ele {
      if cnt > 0 {
        cnt := cnt - 1;
      } else {
        buf[w] := s[i2];
        w := w + 1;
      }
    } else {
      buf[w] := s[i2];
      w := w + 1;
    }
    i2 := i2 + 1;
  }
  output := buf[0..w];
}
