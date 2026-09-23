// 722_A. Broken Clock  (problem 2700, solution 2700_137)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = int(input())
// h,m = map(int, input().split(':'))
// if m > 59:
//     m = 10 + m % 10
// if a == 24:
//     if h > 23:
//         h = h % 10
// elif h > 12:
//     h = h % 10
// if a == 12 and h == 0:
//     h = 10
// s = str(h)
// if h < 10:
//     s = "0" + s
// s += ":"
// if m < 10:
//     s += "0"
// s += str(m)
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, time: string) returns (output: string, ghost steps: nat)
  requires |time| == 5
  ensures steps <= 20
{
  steps := 1;
  var h := ParseInt(time[0..2]);
  var m := ParseInt(time[3..5]);
  steps := steps + 3;
  if m > 59 {
    m := 10 + m % 10;
  }
  steps := steps + 1;
  if N == 24 {
    if h > 23 {
      h := h % 10;
    }
  } else if h > 12 {
    h := h % 10;
  }
  steps := steps + 2;
  if N == 12 && h == 0 {
    h := 10;
  }
  steps := steps + 1;
  var s := IntToString(h);
  steps := steps + 1;
  if h < 10 {
    s := "0" + s;
  }
  steps := steps + 1;
  s := s + ":";
  steps := steps + 1;
  if m < 10 {
    s := s + "0";
  }
  steps := steps + 1;
  s := s + IntToString(m);
  steps := steps + 2;
  output := s + "\n";
  steps := steps + 1;
}
