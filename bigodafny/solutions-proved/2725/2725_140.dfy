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

method Solve(n: int, k: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |s| + 140
{
  steps := 1;
  var count := seq(26, _ => 0);
  var z := 0;
  ghost var base0 := steps;
  while z < 26
    invariant 0 <= z <= 26
    invariant |count| == 26
    invariant steps <= base0 + 2 * z
    decreases 26 - z
  {
    count := count[z := 0];
    z := z + 1;
    steps := steps + 2;
  }
  var idx := 0;
  ghost var base1 := steps;
  while idx < |s|
    invariant 0 <= idx <= |s|
    invariant |count| == 26
    invariant steps <= base1 + 3 * idx
    decreases |s| - idx
  {
    var pos := (s[idx] as int) - ('a' as int);
    if 0 <= pos < 26 {
      count := count[pos := count[pos] + 1];
    }
    idx := idx + 1;
    steps := steps + 3;
  }
  var deletables := -1;
  var ele := 0;
  var kk := k;
  var countRemaining := 0;
  var found := false;
  var j := 0;
  ghost var base2 := steps;
  while j < 26 && !found
    invariant 0 <= j <= 26
    invariant |count| == 26
    invariant steps <= base2 + 3 * j
    decreases 26 - j
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
    steps := steps + 3;
  }
  var buf := seq(|s|, _ => ' ');
  var w := 0;
  var cnt := countRemaining;
  var i2 := 0;
  ghost var base3 := steps;
  while i2 < |s|
    invariant 0 <= i2 <= |s|
    invariant 0 <= w <= i2
    invariant |buf| == |s|
    invariant steps <= base3 + 4 * i2
    decreases |s| - i2
  {
    var pos := (s[i2] as int) - ('a' as int);
    if pos <= deletables {
      // deleted tier: skip entirely
    } else if pos == ele {
      if cnt > 0 {
        cnt := cnt - 1;
      } else {
        buf := buf[w := s[i2]];
        w := w + 1;
      }
    } else {
      buf := buf[w := s[i2]];
      w := w + 1;
    }
    i2 := i2 + 1;
    steps := steps + 4;
  }
  output := buf[0..w];
  steps := steps + 1;
}
