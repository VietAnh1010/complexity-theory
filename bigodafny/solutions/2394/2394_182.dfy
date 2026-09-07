// 1296_E1. String Coloring (easy version)  (problem 2394, solution 2394_182)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n = int(input())
//     s = input()
//     fst_lst = [s[0]]
//     snd_lst = []
//     ans = '1'
//     for i in range(1, len(s)):
//         if fst_lst[-1]<=s[i]:
//             fst_lst.append(s[i])
//             ans+='1'
//         else:
//             snd_lst.append(s[i])
//             ans+='0'
//     # print (*fst_lst)
//     # print (*snd_lst)
//     if sorted(snd_lst)==snd_lst:
//         print ('YES')
//         print (ans)
//     else:
//         print ('NO')
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_: string) returns (output: string)
  requires |string_| >= 1
{
  var s := string_;
  var m := |s|;
  var ans := new char[m];
  ans[0] := '1';
  var fstLast := s[0];
  var sndOk := true;
  var haveSnd := false;
  var sndLast := s[0];
  var i := 1;
  while i < m
    invariant 1 <= i <= m
  {
    if fstLast <= s[i] {
      fstLast := s[i];
      ans[i] := '1';
    } else {
      if haveSnd && sndLast > s[i] {
        sndOk := false;
      }
      sndLast := s[i];
      haveSnd := true;
      ans[i] := '0';
    }
    i := i + 1;
  }
  if sndOk {
    output := "YES\n" + ans[..] + "\n";
  } else {
    output := "NO\n";
  }
}
