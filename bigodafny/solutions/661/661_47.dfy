// 1323_C. Unusual Competitions  (problem 661, solution 661_47)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n= int(input())
// seq= list(input())
// 
// if seq.count(')')!=seq.count('('):
// 	print(-1)
// else:
// 	a,b=[],[]
// 	for i in range(len(seq)):
// 		if seq[i]==')':
// 			a.append(i)
// 		else:
// 			b.append(i)
// 	c=[]
// 	for i in range(len(a)):
// 		if b[i]>a[i]:
// 			c.append(a[i])
// 			c.append(b[i])
// 	c.sort()
// 	start=0
// 	sum=0
// 	for i in range(len(c)-1):
// 		if c[i]!=c[i+1]-1:
// 			sum+=c[i]-c[start]+1
// 			start=i+1
// 		else:
// 			if i==len(c)-2:
// 				sum+=c[i+1]-c[start]+1
// 			
// 	print(sum)
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var countClose := CountChar661(s, ')');
  var countOpen := CountChar661(s, '(');
  if countClose != countOpen {
    output := "-1";
  } else {
    var a: seq<int> := [];
    var b: seq<int> := [];
    var i := 0;
    while i < |s|
      decreases |s| - i
    {
      if s[i] == ')' { a := a + [i]; } else { b := b + [i]; }
      i := i + 1;
    }
    var c: seq<int> := [];
    i := 0;
    while i < |a|
      decreases |a| - i
    {
      if b[i] > a[i] {
        c := c + [a[i], b[i]];
      }
      i := i + 1;
    }
    c := SortInts(c);
    var start := 0;
    var sum := 0;
    i := 0;
    while i < |c| - 1
      decreases |c| - 1 - i
    {
      if c[i] != c[i+1] - 1 {
        sum := sum + (c[i] - c[start] + 1);
        start := i + 1;
      } else {
        if i == |c| - 2 {
          sum := sum + (c[i+1] - c[start] + 1);
        }
      }
      i := i + 1;
    }
    output := IntToString(sum);
  }
}

method CountChar661(s: string, ch: char) returns (cnt: int)
{
  cnt := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == ch { cnt := cnt + 1; }
    i := i + 1;
  }
}
