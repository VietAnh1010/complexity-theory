// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : unclear
//   confidence     : low
//   auditor        : main agent, override of labelaudit-r4-u01
//
//   Which of the label or the translation is at fault was not determined
//   by the audit.
//
//   evidence:
//     Override of labelaudit-r4-u01's mismatch: each cell string (e.g.
//     R23C55) encodes two machine-word numbers, and FirstDigitIndex,
//     DigitRunLen, ParseInt and LettersToNum walk it; whether that width
//     is a size is the open ParseInt question, so the verdict waits on it.
//
//   how this label could be wrong, and what to check:
//     The verdict turns on whether a numeral token's width is a size. The
//     brief charges ParseInt its argument's length; the proofs (378_91,
//     976_1131) charge it 1, as IntToString is. Settle the ParseInt charge
//     in COMPLEXITY.md, then re-file: width as a size gives O(n*m), a
//     machine-word token gives O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 85, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "ParseInt",
//     "ParseIntFrom"], "loop_depth": 1, "loops": 1, "recursive_helpers":
//     6, "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
      assert forall k :: 0 <= k < |colDigits| ==> '0' <= colDigits[k] <= '9';
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
