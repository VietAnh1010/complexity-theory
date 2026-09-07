// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_144)
// time complexity: O(n+m)log(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// aa,bb=map(int, input().split())
// s=input()
// kiri=[]
// tupl=[]
// ini=[]
// cetak=""
// for i in range(len(s)):
// 	if s[i]=="(":
// 		kiri.append(i)
// 	else:
// 		tupl.append((kiri.pop(),i))
// tupl=tupl[:bb//2]
// for k in tupl:
// 	ini.extend(k)
// ini.sort()
// for j in ini:
// 	cetak+=s[j]
// print(cetak)
// 			   	 	   	  		 	 	 		 				 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  var kiri: seq<int> := [];
  var tupl: seq<(int,int)> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
  {
    if s[i] == '(' {
      kiri := kiri + [i];
    } else {
      tupl := tupl + [(kiri[|kiri|-1], i)];
      kiri := kiri[..|kiri|-1];
    }
    i := i + 1;
  }
  var take := if m/2 <= |tupl| then m/2 else |tupl|;
  if take < 0 { take := 0; }
  tupl := tupl[..take];
  var ini: seq<int> := [];
  var k := 0;
  while k < |tupl|
    invariant 0 <= k <= |tupl|
  {
    ini := ini + [tupl[k].0, tupl[k].1];
    k := k + 1;
  }
  ini := SortInts(ini);
  var cetak := "";
  var j := 0;
  while j < |ini|
    invariant 0 <= j <= |ini|
  {
    cetak := cetak + [s[ini[j]]];
    j := j + 1;
  }
  output := cetak + "\n";
}
