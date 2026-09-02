// 1328_B. K-th Beautiful String  (problem 2819, solution 2819_55)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// 
// for _ in range(int(input())):
//     n, k = map(int, input().split())
//     ans = ['a']*n
//     for i, right in zip(range(n-2, -1, -1), range(1, n+1)):
//         if k > right:
//             k -= right
//             continue
//         j = n
//         while k:
//             k -= 1
//             j -= 1
// 
//         ans[i] = ans[j] = 'b'
//         break
// 
//     print(*ans, sep='')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
  {
    var row := pairs_list[t];
    if |row| >= 2 {
      var nn := row[0];
      var kk := row[1];
      var sz := if nn > 0 then nn else 0;
      var buf := new char[sz];
      var z := 0;
      while z < sz
        invariant 0 <= z <= sz
      {
        buf[z] := 'a';
        z := z + 1;
      }
      var i := nn - 2;
      var right := 1;
      var found := false;
      while i >= 0 && !found
        decreases i + 1
      {
        if kk > right {
          kk := kk - right;
        } else {
          var j := nn;
          var kk0 := kk;
          while kk > 0
            invariant j == nn - (kk0 - kk)
            decreases kk
          {
            kk := kk - 1;
            j := j - 1;
          }
          if 0 <= i < sz { buf[i] := 'b'; }
          if 0 <= j < sz { buf[j] := 'b'; }
          found := true;
        }
        i := i - 1;
        right := right + 1;
      }
      results := results + [buf[0..sz]];
    }
    t := t + 1;
  }
  output := Join(results, "\n");
}
