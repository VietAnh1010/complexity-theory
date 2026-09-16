// 8_B. Obsession with Robots  (problem 949, solution 949_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// x,y=0,0
// used=set()
// used.add((x,y))
// bo=0
// for e in s:
//     if(e=='L'):
//         x+=1
//     elif(e=='R'):
//         x-=1
//     elif(e=='U'):
//         y+=1
//     else:
//         y-=1
//     a=(x-1,y) in used
//     b=(x+1,y) in used
//     c=(x,y-1) in used
//     d=(x,y+1) in used
//     if(a+b+c+d>1):
//         bo=1
//     if((x,y) in used):
//         bo=1
//     used.add((x,y))
// print("OK" if not bo else "BUG")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(directions: string) returns (output: string)
{
  var x := 0;
  var y := 0;
  var used: set<(int, int)> := {(0, 0)};
  var bo := false;
  var i := 0;
  while i < |directions|
    decreases |directions| - i
  {
    var e := directions[i];
    if e == 'L' {
      x := x + 1;
    } else if e == 'R' {
      x := x - 1;
    } else if e == 'U' {
      y := y + 1;
    } else {
      y := y - 1;
    }
    var a := (x - 1, y) in used;
    var b := (x + 1, y) in used;
    var c := (x, y - 1) in used;
    var d := (x, y + 1) in used;
    var cnt := (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0);
    if cnt > 1 {
      bo := true;
    }
    if (x, y) in used {
      bo := true;
    }
    used := used + {(x, y)};
    i := i + 1;
  }
  output := (if !bo then "OK" else "BUG") + "\n";
}
