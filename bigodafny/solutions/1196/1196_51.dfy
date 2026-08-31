// 53_A. Autocomplete  (problem 1196, solution 1196_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// n = int(input())
// l = []
// for i in range(n):
// 	l.append(input())
// k = len(s)
// answer = ""
// for a in l:
// 	if a[:k]==s:
// 		if a<answer or answer =="":
// 			answer=a
// if answer:
// 	print(answer)
// else:
// 	print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string, n: int, text_list: seq<string>) returns (output: string)
{
  var k := |text|;
  var answer := "";
  var i := 0;
  while i < n
    decreases n - i
  {
    var a := text_list[i];
    if |a| >= k && a[..k] == text {
      if answer == "" || StringLess(a, answer) {
        answer := a;
      }
    }
    i := i + 1;
  }
  if answer != "" {
    output := answer;
  } else {
    output := text;
  }
}

function StringLess(a: string, b: string): bool
{
  if |a| == 0 then |b| > 0
  else if |b| == 0 then false
  else if a[0] != b[0] then a[0] < b[0]
  else StringLess(a[1..], b[1..])
}
