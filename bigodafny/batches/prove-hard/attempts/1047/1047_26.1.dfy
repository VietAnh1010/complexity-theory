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

include "../../../../prelude.dfy"

function FirstDigitIndex(s: string, i: nat): nat
  requires i <= |s|
  ensures i <= FirstDigitIndex(s, i) <= |s|
  decreases |s| - i
{
  if i >= |s| then
    i
  else if '0' <= s[i] <= '9' then
    i
  else
    FirstDigitIndex(s, i + 1)
}

ghost function FirstDigitIndex_steps(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  3 + if i >= |s| then 0 else 6 + if '0' <= s[i] <= '9' then 0 else 1 + FirstDigitIndex_steps(s, i + 1)
}

function DigitRunLen(s: string, i: nat): nat
  requires i <= |s|
  ensures i + DigitRunLen(s, i) <= |s|
  ensures forall j :: i <= j < i + DigitRunLen(s, i) ==> '0' <= s[j] <= '9'
  decreases |s| - i
{
  if i < |s| && '0' <= s[i] <= '9' then
    1 + DigitRunLen(s, i + 1)
  else
    0
}

ghost function DigitRunLen_steps(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  4 + (if i < |s| then 5 else 0) + if i < |s| && '0' <= s[i] <= '9' then 2 + DigitRunLen_steps(s, i + 1) else 0
}

function LettersToNum(s: string): int
  decreases |s|
{
  if |s| == 0 then
    0
  else
    LettersToNum(s[..|s| - 1]) * 26 + (s[|s| - 1] as int - 'A' as int + 1)
}

ghost function LettersToNum_steps(s: string): nat
  decreases |s|
{
  3 + if |s| == 0 then 0 else 12 + LettersToNum_steps(s[..|s| - 1])
}

function NumToLetters(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then
    ""
  else if n % 26 == 0 then
    NumToLetters(n / 26 - 1) + "Z"
  else
    NumToLetters(n / 26) + ["ABCDEFGHIJKLMNOPQRSTUVWXYZ"[n % 26 - 1]]
}

ghost function NumToLetters_steps(n: int): nat
  requires n >= 0
  decreases n
{
  2 + if n == 0 then 0 else 3 + if n % 26 == 0 then 2 + NumToLetters_steps(n / 26 - 1) + |"Z"| else 5 + NumToLetters_steps(n / 26) + |["ABCDEFGHIJKLMNOPQRSTUVWXYZ"[n % 26 - 1]]|
}

lemma DRLBound(s: string, i: nat)
  requires i <= |s|
  ensures DigitRunLen_steps(s, i) <= 11 * (|s| - i) + 9
  decreases |s| - i
{
  if i < |s| && '0' <= s[i] <= '9' { DRLBound(s, i + 1); }
}

lemma FDIBound(s: string, i: nat)
  requires i <= |s|
  ensures FirstDigitIndex_steps(s, i) <= 10 * (|s| - i) + 3
  decreases |s| - i
{
  if i < |s| && !('0' <= s[i] <= '9') { FDIBound(s, i + 1); }
}

lemma LTNBound(s: string)
  ensures LettersToNum_steps(s) <= 12 * |s| + 3
  decreases |s|
{
  if |s| > 0 { LTNBound(s[..|s| - 1]); }
}

lemma NTLBound(n: int)
  requires n >= 0
  ensures NumToLetters_steps(n) <= 9 * |NumToLetters(n)| + 2
  decreases n
{
  if n > 0 {
    if n % 26 == 0 { NTLBound(n / 26 - 1); } else { NTLBound(n / 26); }
  }
}

method Solve(n: int, strings: seq<string>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 71 * |strings| + 70 * SumLen(strings) + 11 * |output| + 2
{
  steps := 0;
  var lines: seq<string> := [];
  var idx := 0;
  assert strings[..0] == [];
  while idx < |strings|
    invariant 0 <= idx <= |strings|
    invariant |lines| == idx
    invariant steps <= 70 * (idx + SumLen(strings[..idx])) + 10 * SumLen(lines)
    decreases |strings| - idx
  {
    ghost var s0 := steps;
    ghost var sl0 := SumLen(lines);
    steps := steps + 3;
    steps := steps + 1;
    var cell := strings[idx];
    var isRC := false;
    var d1 := 0;
    steps := steps + (3 + if |cell| > 0 then 2 else 0);
    if |cell| > 0 && cell[0] == 'R' {
      DRLBound(cell, 1);
      steps := steps + DigitRunLen_steps(cell, 1);
      d1 := DigitRunLen(cell, 1);
      steps := steps + (3 + (if d1 > 0 then 3 else 0) + if d1 > 0 && 1 + d1 < |cell| then 3 else 0);
      if d1 > 0 && 1 + d1 < |cell| && cell[1 + d1] == 'C' {
        DRLBound(cell, 1 + d1 + 1);
        steps := steps + (2 + DigitRunLen_steps(cell, 1 + d1 + 1));
        var d2 := DigitRunLen(cell, 1 + d1 + 1);
        steps := steps + (2 + if d2 > 0 then 5 else 0);
        if d2 > 0 && 1 + d1 + 1 + d2 == |cell| {
          isRC := true;
        }
      }
    }
    if isRC {
      steps := steps + 2;
      var rowDigits := cell[1 .. 1 + d1];
      steps := steps + 3;
      var colDigits := cell[1 + d1 + 1..];
      assert forall k :: 0 <= k < |colDigits| ==> '0' <= colDigits[k] <= '9';
      steps := steps + |colDigits|;
      var colNum := ParseInt(colDigits);
      NTLBound(colNum);
      steps := steps + (1 + NumToLetters_steps(colNum) + |rowDigits| + |[NumToLetters(colNum) + rowDigits]|);
      SumLenSnoc(lines, NumToLetters(colNum) + rowDigits);
      lines := lines + [NumToLetters(colNum) + rowDigits];
      assert steps + 1 <= s0 + 70 * (|cell| + 1) + 10 * (SumLen(lines) - sl0);
    } else {
      FDIBound(cell, 0);
      steps := steps + FirstDigitIndex_steps(cell, 0);
      var fd := FirstDigitIndex(cell, 0);
      steps := steps + 1;
      var colLetters := cell[..fd];
      steps := steps + 1;
      var rowDigits := cell[fd..];
      LTNBound(colLetters);
      steps := steps + LettersToNum_steps(colLetters);
      var colNum := LettersToNum(colLetters);
      IntToStringDigits(colNum);
      steps := steps + (1 + |rowDigits| + |"C"| + Digits(colNum) + |IntToString(colNum)| + |["R" + rowDigits + "C" + IntToString(colNum)]|);
      SumLenSnoc(lines, "R" + rowDigits + "C" + IntToString(colNum));
      lines := lines + ["R" + rowDigits + "C" + IntToString(colNum)];
      assert steps + 1 <= s0 + 70 * (|cell| + 1) + 10 * (SumLen(lines) - sl0);
    }
    steps := steps + 1;
    assert strings[..idx + 1] == strings[..idx] + [cell];
    SumLenSnoc(strings[..idx], cell);
    idx := idx + 1;
  }
  assert strings[..idx] == strings;
  steps := steps + 2;
  steps := steps + (SumLen(lines) + |lines|);
  output := Join(lines, "\n");
  if |lines| > 0 { JoinLen(lines, "\n"); } else { assert lines == []; }
}

import opened Prelude
