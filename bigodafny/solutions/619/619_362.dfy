// 975_A. Aramic script  (problem 619, solution 619_362)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=str(input()) 
// arr = [str(x) for x in input().split()]
// 
// 
// ss = set()
// 
// for x in arr:
//       a2 = []
//       s=""
//       for i in range(int(26)):
//               a2.append(0)
//       for i in range(len(x)):
//               nu = ord(x[i]) 
//               nu = nu - ord('a')
//               a2[nu]=1 
//       for i in range(int(26)): 
//             if a2[i]==1:
//                 s=s+str(chr(i +ord('a'))) 
//       ss.add(s) 
// 
// 
// print(len(ss))
//       
//        
//      
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var sigs: seq<string> := [];
  var i := 0;
  while i < |strings|
    decreases |strings| - i
  {
    var sg := Signature619b(strings[i]);
    sigs := sigs + [sg];
    i := i + 1;
  }
  var distinctCount := CountDistinct619b(sigs);
  output := IntToString(distinctCount);
}

method Signature619b(s: string) returns (sig: string)
{
  var pres := seq(26, _ => false);
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    var idx := (s[i] as int) - ('a' as int);
    if 0 <= idx < 26 {
      pres := pres[idx := true];
    }
    i := i + 1;
  }
  var alphabet := "abcdefghijklmnopqrstuvwxyz";
  sig := "";
  i := 0;
  while i < 26
    decreases 26 - i
  {
    if pres[i] {
      sig := sig + [alphabet[i]];
    }
    i := i + 1;
  }
}

method CountDistinct619b(xs: seq<string>) returns (c: int)
{
  var seen: seq<string> := [];
  var i := 0;
  while i < |xs|
    decreases |xs| - i
  {
    if xs[i] !in seen {
      seen := seen + [xs[i]];
    }
    i := i + 1;
  }
  c := |seen|;
}
