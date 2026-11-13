include "../../prelude.dfy"
import opened Prelude

method Solve(text: string) returns (output: string, ghost steps: nat)
  ensures steps <= 26 * (8 * |text| + 8) + 2 * |output| + 30
{
  steps := 1;
  ghost var K: nat := 8 * |text| + 8;
  var lines: seq<string> := [];
  var letter := 0;
  while letter < 26
    invariant 0 <= letter <= 26
    invariant |lines| == letter
    invariant steps <= 1 + letter * K + SumLen(lines) + 2 * letter
    decreases 26 - letter
  {
    var c: char := (97 + letter) as char;
    var count := 0;
    var i := 0;
    ghost var s0 := steps;
    while i < |text|
      invariant 0 <= i <= |text|
      invariant steps <= s0 + 8 * i
      decreases |text| - i
    {
      var ch := text[i];
      var lc: char := if ch >= 'A' && ch <= 'Z' then ((ch as int) + 32) as char else ch;
      if lc == c {
        count := count + 1;
      }
      i := i + 1;
      steps := steps + 8;
    }
    var line := [c] + " : " + IntToString(count);
    IntToStringDigits(count);
    SumLenSnoc(lines, line);
    lines := lines + [line];
    steps := steps + 8 + |line| + 2;
    letter := letter + 1;
    CostMulDistrib(letter - 1, 1, letter, K);
  }
  JoinLen(lines, "\n");
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
}
