// 988_B. Substrings Sort  (problem 1272, solution 1272_115)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// list1=[]
// for i in range(n):
//     s=input()
//     list1.append(s)
// # list1.sort()
// for i in range(n-1):
//     for j in range(i,n):
//         if(len(list1[i])>len(list1[j])):
//             list1[i],list1[j]=list1[j],list1[i]
// f=0
// for i in range(n-1):
//     # if(list1[i] in list1[i+1]):
//     x=list1[i+1].find(list1[i])
//     if(x>=0):
//         continue
//     else:
//         f=1
// if(f==0):
//     print("YES")
//     for i in range(n):
//         print(list1[i])
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsFrom1272a(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then false
  else if hay[pos..pos+|needle|] == needle then true
  else ContainsFrom1272a(hay, needle, pos + 1)
}

function Contains1272a(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272a(hay, needle, 0)
}

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var list1 := strings;
  var i := 0;
  while i < n - 1
    decreases n - 1 - i
  {
    var j := i;
    while j < n
      decreases n - j
    {
      if |list1[i]| > |list1[j]| {
        var tmp := list1[i];
        list1 := list1[i := list1[j]][j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  var f := 0;
  var k := 0;
  while k < n - 1
    decreases n - 1 - k
  {
    if !Contains1272a(list1[k+1], list1[k]) { f := 1; }
    k := k + 1;
  }
  if f == 0 {
    var lines: seq<string> := ["YES"];
    var m := 0;
    while m < n
      decreases n - m
    {
      lines := lines + [list1[m]];
      m := m + 1;
    }
    output := Join(lines, "\n");
  } else {
    output := "NO";
  }
}
