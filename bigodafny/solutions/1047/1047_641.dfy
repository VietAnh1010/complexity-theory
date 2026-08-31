// 1_B. Spreadsheets  (problem 1047, solution 1047_641)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import re
// 
// for t in range(int(input())):
// 	a = input()
// 
// 	if re.search("R\d+C\d+",a):
// 		row,col= a.split("C")
// 		row = row[1:]
// 		col = int(col)
// 
// 		ans = ""
// 
// 		while col:
// 			temp = col%26+64
// 			if temp == 64:
// 				temp = 90
// 				col-=1
// 			ans = chr(temp) + ans
// 			col//=26
// 		print(ans+row)
// 	else:
// 
// 		col = ""
// 
// 		for i in a:
// 			if i.isalpha():
// 				col+=i
// 			else:
// 				break
// 
// 		row = a.replace(col,"")
// 
// 		ans = 0
// 
// 
// 		for i in col:
// 			ans = 26*ans + (ord(i)-64)
// 
// 		print("R"+row+"C"+str(ans))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var lines: seq<string> := [];
  var idx := 0;
  while idx < |strings|
    decreases |strings| - idx
  {
    var a := strings[idx];
    if IsRCFormat(a) {
      var i := DigitRunEnd(a, 1);
      var row := a[1..i];
      var j := DigitRunEnd(a, i + 1);
      var colStr := a[i + 1..j];
      var col := ParseInt(colStr);
      var letters := ColToLetters(col, "");
      lines := lines + [letters + row];
    } else {
      var k := 0;
      while k < |a| && IsAlpha(a[k])
        decreases |a| - k
      {
        k := k + 1;
      }
      var col := a[0..k];
      var row := a[k..];
      var ans := 0;
      var m := 0;
      while m < |col|
        decreases |col| - m
      {
        ans := 26 * ans + (col[m] as int - 64);
        m := m + 1;
      }
      lines := lines + ["R" + row + "C" + IntToString(ans)];
    }
    idx := idx + 1;
  }
  output := Join(lines, "\n");
}


predicate IsDigit(c: char) { '0' <= c <= '9' }
predicate IsAlpha(c: char) { 'A' <= c <= 'Z' }

function DigitRunEnd(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  if i < |s| && IsDigit(s[i]) then DigitRunEnd(s, i + 1) else i
}

predicate IsRCFormat(s: string)
{
  |s| >= 1 && s[0] == 'R' &&
  (var i := DigitRunEnd(s, 1);
   i > 1 && i < |s| && s[i] == 'C' &&
   (var j := DigitRunEnd(s, i + 1);
    j > i + 1 && j == |s|))
}

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| then acc else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int { ParseIntFrom(s, 0, 0) }

function ColToLetters(col: int, acc: string): string
  decreases col
{
  if col <= 0 then acc
  else
    var temp0 := col % 26 + 64;
    var overflow := temp0 == 64;
    var letterIdx := if overflow then 25 else temp0 - 65;
    var col2 := if overflow then col - 1 else col;
    ColToLetters(col2 / 26, "ABCDEFGHIJKLMNOPQRSTUVWXYZ"[letterIdx..letterIdx + 1] + acc)
}
