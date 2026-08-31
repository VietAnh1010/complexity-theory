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
  output := ""; // TODO: translate the Python above
}
