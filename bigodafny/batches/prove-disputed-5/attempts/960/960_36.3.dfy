// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops over each of the n strings once, inserting into a
//     set of at most 26 letters and sorting that set, so the cost is
//     O(n*m) for n strings of length m, as in the Python.
//
//   how this label could be wrong, and what to check:
//     The code is n test strings each scanned once, plus a sort of at most
//     26 distinct letters per string. By the naming rule that is O(n*m),
//     not one size squared. Check that the sort input `g` is a set of
//     lowercase letters, so it is constant-size.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 47, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     3, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     true, "sorts": ["Sort"], "uses_map": false, "uses_multiset": false,
//     "uses_set": true}
// --------------------------------------------------------------------

// 1251_A. Broken Keyboard  (problem 960, solution 960_36)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
//     s = list(input().strip())
//     g = set()
//     n = len(s)
//     c = 1
//     if n==1:
//         print(s[0])
//     else:
//         for i in range(1,n):
//             if s[i]!=s[i-1] and c&1:
//                 g.add(s[i-1])
//             else:
//                 c += 1
//             if i==n-1 and c&1:
//                 g.add(s[i])
//         print(''.join(sorted(list(g))))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma NLogNSuper(a: nat, b: nat)
  ensures NLogN(a) + NLogN(b) <= NLogN(a + b)
{
  reveal NLogN();
  CeilLog2Monotone(a, a + b);
  CeilLog2Monotone(b, a + b);
  CostMulMono(a, CeilLog2(a) + 1, CeilLog2(a + b) + 1);
  CostMulMono(b, CeilLog2(b) + 1, CeilLog2(a + b) + 1);
  CostMulDistrib(a, b, a + b, CeilLog2(a + b) + 1);
}

lemma SetLen(s: string)
  ensures |set c | c in s| <= |s|
  decreases |s|
{
  if |s| > 0 {
    SetLen(s[1..]);
    assert (set c | c in s) == {s[0]} + (set c | c in s[1..]);
  }
}

method Solve(n: int, strings: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 25 * |strings| + 20 * SumLen(strings) + 2 * NLogN(SumLen(strings)) + 10 + 3 * |output|
{
  steps := 3;
  var lines: seq<string> := [];
  var si := 0;
  while si < |strings|
    invariant 0 <= si <= |strings|
    invariant |lines| == si
    invariant steps <= 3 + 25 * si + 20 * SumLen(strings[..si]) + 2 * NLogN(SumLen(strings[..si]))
    decreases |strings| - si
  {
    var s := strings[si];
    var m := |s|;
    ghost var tot := SumLen(strings[..si]);
    assert strings[..si + 1] == strings[..si] + [s];
    SumLenSnoc(strings[..si], s);
    NLogNSuper(tot, m);
    SumLenPrefix(strings, si + 1);
    ghost var base := steps;
    steps := steps + 8;
    var lineOut: string;
    if m == 1 {
      lineOut := [s[0]];
      steps := steps + 3;
    } else {
      var g: set<char> := {};
      var c := 1;
      var i := 1;
      SetLen(s);
      ghost var bs := set c | c in s;
      while i < m
        invariant 1 <= i || m == 0
        invariant i <= m || m == 0
        invariant g <= bs
        invariant steps <= base + 8 + 12 * (i - 1)
        decreases m - i
      {
        steps := steps + 12;
        if s[i] != s[i-1] && c % 2 == 1 {
          g := g + {s[i-1]};
        } else {
          c := c + 1;
        }
        if i == m-1 && c % 2 == 1 {
          g := g + {s[i]};
        }
        i := i + 1;
      }
      assert bs == g + (bs - g);
      assert |g| <= |bs|;
      var elems: seq<char> := [];
      var gg := g;
      ghost var base2 := steps;
      while gg != {}
        invariant gg <= g
        invariant |elems| + |gg| == |g|
        invariant steps <= base2 + 6 * |elems|
        decreases |gg|
      {
        var x :| x in gg;
        elems := elems + [x];
        gg := gg - {x};
        steps := steps + 6;
      }
      assert |gg| == 0;
      assert |bs| <= m;
      assert |elems| <= m;
      lineOut := Sort(elems, (a, b) => a < b);
      steps := steps + 2 + SortCost(|elems|);
      SortCostNLogN(|elems|);
      NLogNMonotone(|elems|, m);
    }
    SumLenSnoc(lines, lineOut);
    lines := lines + [lineOut];
    si := si + 1;
  }
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
  if |lines| >= 1 { JoinLen(lines, "\n"); }
  assert strings[..|strings|] == strings;
}
