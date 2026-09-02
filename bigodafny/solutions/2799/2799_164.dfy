// 394_A. Counting Sticks  (problem 2799, solution 2799_164)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// l = []
// l = s.split("+")
// temp = l[1].split("=")
// l[1] = temp[0]
// l.append(temp[1])
// a = []
// for i in l:
//     a.append(i.count("|"))
// result = (a[0] + a[1]) - a[2]
// if result == 0:
//     print(s)
// elif result == 2:
//     l[2] += "|"
//     if a[0] == 1:
//         l[1] = l[1][:-1]
//     else:
//         l[0] = l[0][:-1]
//     print(l[0] + "+" + l[1] + "=" + l[2])
// elif result == -2:
//     l[0] += "|"
//     l[2] = l[2][:-1]
//     print(l[0] + "+" + l[1] + "=" + l[2])
// else:
//     print("Impossible")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountChar(s: string, c: char): int
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

method Solve(v_0: seq<string>) returns (output: string)
{
  if |v_0| < 2 {
    output := "";
    return;
  }
  var s := v_0[0] + "+" + v_0[1];
  var l0 := v_0[0];
  var rest := v_0[1];
  var eqIdx := 0;
  var found := false;
  var t := 0;
  while t < |rest|
    invariant 0 <= t <= |rest|
    invariant found ==> 0 <= eqIdx < |rest|
  {
    if !found && rest[t] == '=' {
      eqIdx := t;
      found := true;
    }
    t := t + 1;
  }
  var l1 := if found then rest[..eqIdx] else rest;
  var l2 := if found then rest[eqIdx+1..] else "";

  var a0 := CountChar(l0, '|');
  var a1 := CountChar(l1, '|');
  var a2 := CountChar(l2, '|');
  var result := (a0 + a1) - a2;
  if result == 0 {
    output := s;
  } else if result == 2 {
    var l2b := l2 + "|";
    var l0b := l0;
    var l1b := l1;
    if a0 == 1 {
      l1b := if |l1| > 0 then l1[..|l1|-1] else l1;
    } else {
      l0b := if |l0| > 0 then l0[..|l0|-1] else l0;
    }
    output := l0b + "+" + l1b + "=" + l2b;
  } else if result == -2 {
    var l0b := l0 + "|";
    var l2b := if |l2| > 0 then l2[..|l2|-1] else l2;
    output := l0b + "+" + l1 + "=" + l2b;
  } else {
    output := "Impossible";
  }
}
