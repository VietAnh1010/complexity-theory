// 1271_B. Blocks  (problem 2516, solution 2516_238)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = input()
// 
// 
// def go(s, x):
//   b = [1 if c == 'B' else 0 for c in s]
//   o = []
//   n = len(b)
//   for i in range(n):
//     if b[i] != x:
//       if i + 1 >= n:
//         return 0
//       o += i + 1,
//       b[i + 1] = b[i + 1] ^ 1
//   print(len(o))
//   print(' '.join(map(str, o)))
//   return 1
// 
// 
// if not go(a, 0) and not go(a, 1):
//   print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Go(bIn: seq<int>, x: int) returns (ok: bool, out: string)
  requires forall k :: 0 <= k < |bIn| ==> bIn[k] == 0 || bIn[k] == 1
{
  var b := bIn;
  var n := |b|;
  var ops: seq<int> := [];
  var i := 0;
  var failed := false;
  while i < n && !failed
    invariant 0 <= i <= n
    invariant |b| == n
  {
    if b[i] != x {
      if i + 1 >= n {
        failed := true;
      } else {
        ops := ops + [i + 1];
        b := b[i + 1 := 1 - b[i + 1]];
      }
    }
    i := i + 1;
  }
  if failed {
    ok := false;
    out := "";
  } else {
    ok := true;
    out := IntToString(|ops|) + "\n" + JoinInts(ops, " ") + "\n";
  }
}

method Solve(n: int, is_white_list: seq<bool>) returns (output: string)
{
  var b := seq(|is_white_list|, i requires 0 <= i < |is_white_list| => if is_white_list[i] then 0 else 1);
  var ok0, out0 := Go(b, 0);
  if ok0 {
    output := out0;
  } else {
    var ok1, out1 := Go(b, 1);
    if ok1 {
      output := out1;
    } else {
      output := "-1\n";
    }
  }
}
