// 1373_E. Sum of Digits  (problem 554, solution 554_70)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// sys.setrecursionlimit(10**7)
// 
// for _ in range(int(input())):
// 	N, K = map(int, input().split());ans = float("inf")
// 	for i in range(100 - K):
// 		val = 0
// 		for j in range(i, i + K + 1):val += sum(list(map(int, list(str(j)))))
// 		if (N - val) % (K + 1) == 0 and N >= val:x = int((N - val) // (K + 1));tail = str(x % 9) + str("9") * int(x // 9);ans = min(ans, (int(tail + "0" + str(i)) if i < 10 else int(tail + str(i))))
// 
// 	print(-1) if ans == float("inf") else print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
{

  var results: seq<string> := [];
  var idx := 0;
  while idx < |pairs|
  {
    var N := pairs[idx].0;
    var K := pairs[idx].1;
    var haveAns := false;
    var ans := 0;
    var i := 0;
    while i < 100 - K
    {
      var val := 0;
      var j := i;
      while j <= i + K
      {
        val := val + DigitSum(j);
        j := j + 1;
      }
      if (N - val) % (K + 1) == 0 && N >= val {
        var x := (N - val) / (K + 1);
        var tail := IntToString(x % 9) + RepeatChar('9', x / 9);
        var cand := ParseDecimal(tail + PadTwo(i));
        if !haveAns || cand < ans {
          ans := cand;
          haveAns := true;
        }
      }
      i := i + 1;
    }
    results := results + [if haveAns then IntToString(ans) else "-1"];
    idx := idx + 1;
  }
  output := Join(results, "\n");
}


function DigitSum(x: int): int
  requires x >= 0
{
  if x < 10 then x else x % 10 + DigitSum(x / 10)
}

function RepeatChar(c: char, k: int): string
  requires k >= 0
{
  if k == 0 then "" else [c] + RepeatChar(c, k - 1)
}

function PadTwo(i: int): string
{
  if i < 10 then "0" + IntToString(i) else IntToString(i)
}

function ParseDecimalFrom(s: string, i: int, acc: int): int
  requires 0 <= i <= |s|
{
  if i >= |s| then acc
  else ParseDecimalFrom(s, i + 1, acc * 10 + ((s[i] as int) - ('0' as int)))
}

function ParseDecimal(s: string): int
{
  ParseDecimalFrom(s, 0, 0)
}
