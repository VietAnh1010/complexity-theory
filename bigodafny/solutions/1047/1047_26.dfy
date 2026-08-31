// 1_B. Spreadsheets  (problem 1047, solution 1047_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import re
// 
// 
// f = lambda n: sum((ord(k)-64) * 26**i for i, k in enumerate(str(n)[::-1]))
// 
// g = lambda n: '' if not n else (g(n // 26) + chr(n % 26 + 64) if n % 26 else g(n // 26 - 1) + 'Z')
// 
// for cell in [input() for i in range(int(input()))]:
// 	if re.search('R\d+C\d+', cell):
// 		print(g(int(cell[cell.find('C')+1:])) + cell[1:cell.find('C')])
// 	else:
// 		first_digit_index = re.search('\d', cell).start()
// 		print('R' + cell[first_digit_index:] + 'C' + str(f(cell[:first_digit_index])))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function FirstDigitIndex(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  if i >= |s| then i
  else if '0' <= s[i] <= '9' then i
  else FirstDigitIndex(s, i + 1)
}

function DigitRunLen(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  if i < |s| && '0' <= s[i] <= '9' then 1 + DigitRunLen(s, i + 1) else 0
}

function LettersToNum(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else LettersToNum(s[..|s| - 1]) * 26 + (s[|s| - 1] as int - 'A' as int + 1)
}

function NumToLetters(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then ""
  else if n % 26 == 0 then NumToLetters(n / 26 - 1) + "Z"
  else NumToLetters(n / 26) + ["ABCDEFGHIJKLMNOPQRSTUVWXYZ"[n % 26 - 1]]
}

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  ParseIntFrom(s, 0, 0)
}


method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var lines: seq<string> := [];
  var idx := 0;
  while idx < |strings|
    decreases |strings| - idx
  {
    var cell := strings[idx];
    var isRC := false;
    var d1 := 0;
    if |cell| > 0 && cell[0] == 'R' {
      d1 := DigitRunLen(cell, 1);
      if d1 > 0 && 1 + d1 < |cell| && cell[1 + d1] == 'C' {
        var d2 := DigitRunLen(cell, 1 + d1 + 1);
        if d2 > 0 && 1 + d1 + 1 + d2 == |cell| {
          isRC := true;
        }
      }
    }
    if isRC {
      var rowDigits := cell[1..1 + d1];
      var colDigits := cell[1 + d1 + 1..];
      var colNum := ParseInt(colDigits);
      lines := lines + [NumToLetters(colNum) + rowDigits];
    } else {
      var fd := FirstDigitIndex(cell, 0);
      var colLetters := cell[..fd];
      var rowDigits := cell[fd..];
      var colNum := LettersToNum(colLetters);
      lines := lines + ["R" + rowDigits + "C" + IntToString(colNum)];
    }
    idx := idx + 1;
  }
  output := Join(lines, "\n");
}
