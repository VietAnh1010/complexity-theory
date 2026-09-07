// 901_A. Hashing Trees  (problem 2723, solution 2723_27)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// *a, = map(int, input().split())
// b, c = [0], [0]
// cur = 1
// for i in range(1, n + 1):
//     for j in range(a[i]):
//         b.append(cur)
//     cur += a[i]
// cur = 1
// for i in range(1, n + 1):
//     if a[i] > 1 and a[i - 1] > 1:
//         c.append(cur - 1)
//         for j in range(1, a[i]):
//             c.append(cur)
//     else:
//         for j in range(a[i]):
//             c.append(cur)
//     cur += a[i]
// if b == c:
//     exit(print('perfect'))
// print('ambiguous')
// print(*b)
// print(*c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n + 1
  requires n >= 0
{
  var lenB := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    lenB := lenB + a_list[i];
    i := i + 1;
  }
  var lenC := 1;
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    lenC := lenC + a_list[i];
    i := i + 1;
  }
  if lenB < 1 { lenB := 1; }
  if lenC < 1 { lenC := 1; }

  var bArr := new int[lenB];
  bArr[0] := 0;
  var pos := 1;
  var cur := 1;
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    var j := 0;
    while j < a_list[i]
      invariant 0 <= j
    {
      if pos < lenB {
        bArr[pos] := cur;
      }
      pos := pos + 1;
      j := j + 1;
    }
    cur := cur + a_list[i];
    i := i + 1;
  }

  var cArr := new int[lenC];
  cArr[0] := 0;
  pos := 1;
  cur := 1;
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    if a_list[i] > 1 && a_list[i - 1] > 1 {
      if pos < lenC { cArr[pos] := cur - 1; }
      pos := pos + 1;
      var j := 1;
      while j < a_list[i]
        invariant 1 <= j
      {
        if pos < lenC { cArr[pos] := cur; }
        pos := pos + 1;
        j := j + 1;
      }
    } else {
      var j := 0;
      while j < a_list[i]
        invariant 0 <= j
      {
        if pos < lenC { cArr[pos] := cur; }
        pos := pos + 1;
        j := j + 1;
      }
    }
    cur := cur + a_list[i];
    i := i + 1;
  }

  var bSeq := bArr[..];
  var cSeq := cArr[..];
  if bSeq == cSeq {
    output := "perfect\n";
  } else {
    output := "ambiguous\n" + JoinInts(bSeq, " ") + "\n" + JoinInts(cSeq, " ") + "\n";
  }
}
