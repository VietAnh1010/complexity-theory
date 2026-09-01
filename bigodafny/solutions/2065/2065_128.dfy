// 192_A. Funky Numbers  (problem 2065, solution 2065_128)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #codeforces.com:3.2.5(2.4.0)
// import math
// a=int(input())*2;b=0
// for i in range(1,int(math.sqrt(a))):
//     c=a-i*i-i;d=int(math.sqrt(c))
//     if d*(d+1)==c:b=1
// print("YES")if(b)else print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var a := n * 2;
  var b := 0;

  var lo := 0;
  var hi := a + 1;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi + 1) / 2;
    if mid * mid <= a {
      lo := mid;
    } else {
      hi := mid - 1;
    }
  }
  var lim := lo;

  var i := 1;
  while i < lim
    decreases lim - i
  {
    var c := a - i * i - i;
    if c >= 0 {
      var dlo := 0;
      var dhi := c + 1;
      while dlo < dhi
        decreases dhi - dlo
      {
        var mid2 := (dlo + dhi + 1) / 2;
        if mid2 * mid2 <= c {
          dlo := mid2;
        } else {
          dhi := mid2 - 1;
        }
      }
      var d := dlo;
      if d * (d + 1) == c {
        b := 1;
      }
    }
    i := i + 1;
  }

  if b == 1 {
    output := "YES";
  } else {
    output := "NO";
  }
}
