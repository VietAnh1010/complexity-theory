// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : io-rule-2026-10-14
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     One pass over the n cells, but two kinds of work beyond the one read
//     and one write. IsRCFormat scans each cell to pick its format, then
//     DigitRunEnd finds the same boundaries again: a second pass, O(m) per
//     cell for cell length m. ColToLetters prepends each letter (letter +
//     acc copies acc), so a k-letter column costs about k*k/2 with k
//     growing as log of the column VALUE. Class O(n*m + n*log^2 C), not a
//     label class; never O(n**2).
//
//   how this label could be wrong, and what to check:
//     The label squares n, but no step pairs two cells. Check the loop
//     `while idx < |strings|`: per cell it does a second boundary scan and
//     a prepend-built column string, both bounded by that cell's own text
//     and column value.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 76, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "ParseInt",
//     "ParseIntFrom"], "loop_depth": 2, "loops": 3, "recursive_helpers":
//     3, "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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

ghost function Cb(m: nat): nat { 6 * (m + 1) * (m + 10) }

ghost function SumCb(ss: seq<string>): nat
  decreases |ss|
{
  if |ss| == 0 then 0 else SumCb(ss[..|ss| - 1]) + Cb(|ss[|ss| - 1]|)
}

ghost function LC(col: int): nat
  decreases col
{
  if col <= 0 then 0
  else
    var c2 := if col % 26 + 64 == 64 then col - 1 else col;
    1 + LC(c2 / 26)
}

ghost function CLCost(col: int, a: nat): nat
  decreases col
{
  if col <= 0 then 1
  else
    var c2 := if col % 26 + 64 == 64 then col - 1 else col;
    7 + a + CLCost(c2 / 26, a + 1)
}

lemma ClBound(col: int, a: nat)
  ensures CLCost(col, a) <= LC(col) * (LC(col) + a + 8) + 1
  decreases col
{
  if col > 0 {
    var c2 := if col % 26 + 64 == 64 then col - 1 else col;
    ClBound(c2 / 26, a + 1);
    var k := LC(c2 / 26);
    assert (k + 1) * (k + 1 + a + 8) == k * (k + a + 9) + (k + a + 9) + 0 * a + 0;
  }
}

lemma LCDigits(col: int)
  requires col > 0
  ensures LC(col) <= Digits(col)
{
  var c2 := if col % 26 + 64 == 64 then col - 1 else col;
  if c2 / 26 > 0 {
    LCDigits(c2 / 26);
    DigitsMono(c2 / 26, col / 10);
  }
}

lemma DigitsStep(acc: int, d: int)
  requires acc >= 0 && 0 <= d <= 9
  ensures Digits(acc * 10 + d) <= Digits(acc) + 1
{
  assert (acc * 10 + d) / 10 == acc;
}

lemma ParseFromDigits(s: string, i: nat, acc: int)
  requires acc >= 0
  ensures Digits(ParseIntFrom(s, i, acc)) <= Digits(acc) + (if i < |s| then |s| - i else 0)
  decreases |s| - i
{
  if i < |s| && '0' <= s[i] <= '9' {
    DigitsStep(acc, s[i] as int - '0' as int);
    ParseFromDigits(s, i + 1, acc * 10 + (s[i] as int - '0' as int));
  }
}

lemma ParseDigits(s: string)
  ensures ParseInt(s) > 0 ==> Digits(ParseInt(s)) <= |s| + 1
{
  if |s| > 0 && s[0] != '-' {
    ParseFromDigits(s, if s[0] == '+' then 1 else 0, 0);
    assert Digits(0) == 1;
  }
}

lemma RunEndBounds(s: string, i: nat)
  requires i <= |s|
  ensures i <= DigitRunEnd(s, i) <= |s|
  decreases |s| - i
{
  if i < |s| && IsDigit(s[i]) { RunEndBounds(s, i + 1); }
}

lemma CellBound(m: nat, k: nat)
  requires k <= m + 1
  ensures 6 * m + 30 + (k * (k + 8) + 1) <= Cb(m)
  ensures 12 * m + 30 <= Cb(m)
{
  CostMulMonoLeft(k, m + 1, k + 8);
  CostMulMono(m + 1, k + 8, m + 9);
  assert k * (k + 8) <= (m + 1) * (m + 9);
  assert Cb(m) == 6 * ((m + 1) * (m + 10));
  assert (m + 1) * (m + 10) == (m + 1) * (m + 9) + (m + 1);
}

method Solve(n: int, strings: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 3 * SumCb(strings) + 2 * |output| + 5
{
  steps := 1;
  var lines: seq<string> := [];
  var idx := 0;
  while idx < |strings|
    invariant 0 <= idx <= |strings|
    invariant |lines| == idx
    invariant steps <= 1 + SumCb(strings[..idx]) + SumLen(lines) + idx
    invariant idx <= SumCb(strings[..idx])
    decreases |strings| - idx
  {
    ghost var s0 := steps;
    var a := strings[idx];
    assert strings[..idx + 1][..idx] == strings[..idx];
    var m := |a|;
    if IsRCFormat(a) {
      var i := DigitRunEnd(a, 1);
      var row := a[1..i];
      var j := DigitRunEnd(a, i + 1);
      var colStr := a[i + 1..j];
      var col := ParseInt(colStr);
      var letters := ColToLetters(col, "");
      lines := lines + [letters + row];
      RunEndBounds(a, 1);
      ParseDigits(colStr);
      ClBound(col, 0);
      if col > 0 { LCDigits(col); }
      CellBound(m, if col > 0 then LC(col) else 0);
      assert |colStr| <= m;
      assert |row| <= m;
      steps := steps + 6 * m + 30 + CLCost(col, 0);
    } else {
      var k := 0;
      ghost var l0 := steps;
      while k < |a| && IsAlpha(a[k])
        invariant 0 <= k <= |a|
        invariant steps <= l0 + 5 * k
        decreases |a| - k
      {
        k := k + 1;
        steps := steps + 5;
      }
      var col := a[0..k];
      var row := a[k..];
      var ans := 0;
      var mm := 0;
      ghost var l1 := steps;
      while mm < |col|
        invariant 0 <= mm <= |col|
        invariant steps <= l1 + 6 * mm
        decreases |col| - mm
      {
        ans := 26 * ans + (col[mm] as int - 64);
        mm := mm + 1;
        steps := steps + 6;
      }
      IntToStringDigits(ans);
      lines := lines + ["R" + row + "C" + IntToString(ans)];
      CellBound(m, 0);
      steps := steps + 2 * m + 30 + Digits(ans);
    }
    SumLenSnoc(lines[..idx], lines[idx]);
    assert lines[..idx + 1] == lines[..idx] + [lines[idx]];
    idx := idx + 1;
    steps := steps + 1;
  }
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
  if |lines| >= 1 { JoinLen(lines, "\n"); }
  assert strings[..|strings|] == strings;
  assert |lines| > 0 || SumLen(lines) == 0;
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
