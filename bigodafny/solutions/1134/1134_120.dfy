// 1272_A. Three Friends  (problem 1134, solution 1134_120)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def dis(a,b,c):
// 	return abs(a-b)+abs(b-c)+abs(a-c);
// t=int(input());
// while(t>0):
// 	t-=1;
// 	l=list(map(int,input().split()));
// 	a=l[0];
// 	b=l[1];
// 	c=l[2];
// 	ans=dis(a,b,c);
// 	for i in range(-1,2):
// 		for j in range(-1,2):
// 			for k in range(-1,2):
// 				x=a+i;
// 				y=b+j;
// 				z=c+k;
// 				s=dis(x,y,z);
// 				if(s<ans):
// 					ans=s;
// 	print(ans);
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var t := 0;
  while t < |matrix|
    decreases |matrix| - t
  {
    var row := matrix[t];
    var a := row[0];
    var b := row[1];
    var c := row[2];
    var ans := Dis(a, b, c);
    var i := -1;
    while i <= 1
      decreases 1 - i
    {
      var j := -1;
      while j <= 1
        decreases 1 - j
      {
        var k := -1;
        while k <= 1
          decreases 1 - k
        {
          var s := Dis(a + i, b + j, c + k);
          if s < ans { ans := s; }
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    lines := lines + [IntToString(ans)];
    t := t + 1;
  }
  output := Join(lines, "\n");
}


function Dis(a: int, b: int, c: int): int
{
  AbsInt(a - b) + AbsInt(b - c) + AbsInt(a - c)
}
