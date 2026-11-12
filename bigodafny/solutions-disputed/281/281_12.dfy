// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each pass of while flag costs n*n (oi loop with inner j loop), but
//     the number of passes is set by how many mod reductions the values
//     need, a Euclid-like value term (roughly O(n**2 log max x_i)); the
//     statement cap of 100 does not make it constant. The Python repeats
//     the same while True loop, so the label omits a value term the
//     original also pays.
//
//   how this label could be wrong, and what to check:
//     The label assumes the repeat-until-stable outer loop runs a constant
//     number of rounds. Check the while flag loop in Solve (decreases *):
//     if the number of rounds depends on the values x_i (mod reduction,
//     Euclid-like), the cost carries a value factor; if you can show
//     rounds bounded by a constant independent of values, the label
//     stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 51, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString"], "loop_depth": 3,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 389_A. Fox and Number Game  (problem 281, solution 281_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = eval(input())
// no = list(map(eval,input().split()))
// while True:
//     flag = False
//     for i in no:
//         if i<=0:
//             continue
//         for j in range(n):
//             if no[j]>i:
//                 flag = True
//                 if no[j]%i == 0:
//                     no[j] = i
//                 else:
//                     no[j] = no[j]%i
//     if flag == False:
//         break
// # print(no)
// sum = 0
// for i in no:
//     sum += i
// print(int(sum))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function P(x: int): nat { if x > 0 then x else 0 }

ghost function SP(s: seq<int>): nat
  decreases |s|
{ if |s| == 0 then 0 else P(s[0]) + SP(s[1..]) }

lemma SPUpd(s: seq<int>, j: nat, x: int)
  requires j < |s|
  ensures SP(s[j := x]) + P(s[j]) == SP(s) + P(x)
  decreases |s|
{
  if j > 0 {
    SPUpd(s[1..], j - 1, x);
    assert s[j := x][1..] == s[1..][j - 1 := x];
  } else {
    assert s[0 := x][1..] == s[1..];
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
  var no := a_list;
  var flag := true;
  while flag
    invariant |no| == n
    decreases SP(no) + (if flag then 1 else 0)
  {
    ghost var sp0 := SP(no);
    flag := false;
    var oi := 0;
    while oi < n
      invariant 0 <= oi <= n
      invariant |no| == n
      invariant SP(no) <= sp0
      invariant flag ==> SP(no) < sp0
      decreases n - oi
    {
      var iv := no[oi];
      if iv > 0 {
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant |no| == n
          invariant SP(no) <= sp0
          invariant flag ==> SP(no) < sp0
          decreases n - j
        {
          if no[j] > iv {
            flag := true;
            if no[j] % iv == 0 {
              SPUpd(no, j, iv);
              no := no[j := iv];
            } else {
              SPUpd(no, j, no[j] % iv);
              no := no[j := no[j] % iv];
            }
          }
          j := j + 1;
        }
      }
      oi := oi + 1;
    }
  }
  var total := 0;
  var k := 0;
  while k < |no|
    decreases |no| - k
  {
    total := total + no[k];
    k := k + 1;
  }
  output := IntToString(total);
}
