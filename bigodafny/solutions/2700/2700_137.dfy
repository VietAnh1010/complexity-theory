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

method Solve(N: int, time: string) returns (output: string)
  requires |time| == 5
{
  var h := ParseInt(time[0..2]);
  var m := ParseInt(time[3..5]);
  if m > 59 {
    m := 10 + m % 10;
  }
  if N == 24 {
    if h > 23 {
      h := h % 10;
    }
  } else if h > 12 {
    h := h % 10;
  }
  if N == 12 && h == 0 {
    h := 10;
  }
  var s := IntToString(h);
  if h < 10 {
    s := "0" + s;
  }
  s := s + ":";
  if m < 10 {
    s := s + "0";
  }
  s := s + IntToString(m);
  output := s + "\n";
}
