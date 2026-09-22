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

// n for this row is total input length: the sum of the cell-string lengths.
// Every branch does at most a constant number of scans over the current
// cell (FirstDigitIndex/DigitRunLen/ParseInt/LettersToNum/NumToLetters are
// each a single recursion over a prefix of the cell), so each iteration is
// charged its cell's length, per the "recursive function over a string"
// row of the charge table.
ghost function SumLen(xs: seq<string>): nat
{
  if |xs| == 0 then 0 else |xs[0]| + SumLen(xs[1..])
}

lemma SumLenSnoc(xs: seq<string>, extra: string)
  ensures SumLen(xs + [extra]) == SumLen(xs) + |extra|
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    assert (xs + [extra])[1..] == xs[1..] + [extra];
    SumLenSnoc(xs[1..], extra);
  }
}

function FirstDigitIndex(s: string, i: nat): nat
  requires i <= |s|
  ensures i <= FirstDigitIndex(s, i) <= |s|
  decreases |s| - i
{
  if i >= |s| then i
  else if '0' <= s[i] <= '9' then i
  else FirstDigitIndex(s, i + 1)
}

function DigitRunLen(s: string, i: nat): nat
  requires i <= |s|
  ensures i + DigitRunLen(s, i) <= |s|
  ensures forall j :: i <= j < i + DigitRunLen(s, i) ==> '0' <= s[j] <= '9'
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
  requires acc >= 0
  requires forall k :: i <= k < |s| ==> '0' <= s[k] <= '9'
  ensures ParseIntFrom(s, i, acc) >= 0
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  ensures ParseInt(s) >= 0
{
  ParseIntFrom(s, 0, 0)
}


method Solve(n: int, strings: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 41 * SumLen(strings) + 41 * |strings| + 3
{
  steps := 1;
  var lines: seq<string> := [];
  var idx := 0;
  ghost var base1 := steps;
  while idx < |strings|
    invariant 0 <= idx <= |strings|
    invariant steps <= base1 + 40 * SumLen(strings[..idx]) + 40 * idx
    decreases |strings| - idx
  {
    var cell := strings[idx];
    ghost var cellStart := steps;
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
    steps := steps + 2 * |cell| + 5;
    if isRC {
      var rowDigits := cell[1..1 + d1];
      var colDigits := cell[1 + d1 + 1..];
      assert forall k :: 0 <= k < |colDigits| ==> '0' <= colDigits[k] <= '9';
      var colNum := ParseInt(colDigits);
      steps := steps + |colDigits| + 3;
      lines := lines + [NumToLetters(colNum) + rowDigits];
      steps := steps + |cell| + 3;
    } else {
      var fd := FirstDigitIndex(cell, 0);
      var colLetters := cell[..fd];
      var rowDigits := cell[fd..];
      var colNum := LettersToNum(colLetters);
      steps := steps + 2 * |cell| + 3;
      lines := lines + ["R" + rowDigits + "C" + IntToString(colNum)];
      steps := steps + |cell| + 5;
    }
    assert steps <= cellStart + 6 * |cell| + 19;
    idx := idx + 1;
    steps := steps + 1;
    assert strings[..idx] == strings[..idx-1] + [cell];
    SumLenSnoc(strings[..idx-1], cell);
  }
  assert strings[..idx] == strings;
  assert steps <= 1 + 40 * SumLen(strings) + 40 * |strings|;
  output := Join(lines, "\n");
  steps := steps + SumLen(strings) + |strings| + 2;
}
