// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2+m**2)
//   audited class  : other
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's `while |a| > 0 && |b| > 0 && !found` loop runs until a
//     state `(a, b)` repeats in `mark`, so its trip count is the game
//     length, which no construct bounds by a polynomial in n; the Python
//     loop is the same simulation with `str(a)` keys.
//
//   how this label could be wrong, and what to check:
//     The cost is the number of rounds R times the per-round work, and
//     nothing in the code bounds R by a polynomial: the loop stops only
//     when a deck state repeats or a deck empties. Check whether the
//     problem's analysis bounds the rounds (the statement caps n at 10);
//     if R is unbounded in n, the label is wrong for both programs. Also
//     note the Python pays O(n) per round for `str(a)`, which the Dafny's
//     set membership is charged 1.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 98, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 6, "seq_append_read_in_same_loop":
//     true, "seq_args": 2, "seq_update_in_loop": false,
//     "set_build_in_loop": true, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": true}
// --------------------------------------------------------------------

// 546_C. Soldier and Cards  (problem 2680, solution 2680_65)
// time complexity: O(n**2+m**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import deque
// n = int(input())
// a = deque([int(i) for i in input().split()[1:]])
// b = deque([int(i) for i in input().split()[1:]])
// mark = set()
// ans = 0
// while a and b:
//     if str(a)+" "+str(b) in mark:
//         print(-1)
//         exit()
//     mark.add(str(a)+" "+str(b))
//     ans += 1
//     aa = a.popleft()
//     bb = b.popleft()
//     if aa > bb:
//         a.append(bb)
//         a.append(aa)
//     else:
//         b.append(aa)
//         b.append(bb)
// if a:
//     print(ans,1)
// else:
//     print(ans,2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function AllSeqs(S: set<int>, L: nat): set<seq<int>>
  decreases L
{
  if L == 0 then {[]}
  else set x, t | x in S && t in AllSeqs(S, L - 1) :: [x] + t
}

lemma InAllSeqs(s: seq<int>, S: set<int>)
  requires forall x :: x in s ==> x in S
  ensures s in AllSeqs(S, |s|)
  decreases |s|
{
  if |s| > 0 {
    InAllSeqs(s[1..], S);
    assert s == [s[0]] + s[1..];
    assert s[0] in S && s[1..] in AllSeqs(S, |s| - 1);
    var x, t := s[0], s[1..];
    assert x in S && t in AllSeqs(S, |s| - 1);
    assert [x] + t in AllSeqs(S, |s|);
  }
}

ghost function SeqsUpTo(S: set<int>, N: nat): set<seq<int>>
  decreases N
{
  if N == 0 then AllSeqs(S, 0) else SeqsUpTo(S, N - 1) + AllSeqs(S, N)
}

lemma InSeqsUpTo(s: seq<int>, S: set<int>, N: nat)
  requires |s| <= N
  requires forall x :: x in s ==> x in S
  ensures s in SeqsUpTo(S, N)
  decreases N
{
  if |s| == N {
    InAllSeqs(s, S);
  } else {
    InSeqsUpTo(s, S, N - 1);
  }
}

ghost function States(S: set<int>, N: nat): set<(seq<int>, seq<int>)>
{
  set a, b | a in SeqsUpTo(S, N) && b in SeqsUpTo(S, N) :: (a, b)
}

lemma InStates(a: seq<int>, b: seq<int>, S: set<int>, N: nat)
  requires |a| + |b| == N
  requires forall x :: x in a ==> x in S
  requires forall x :: x in b ==> x in S
  ensures (a, b) in States(S, N)
{
  InSeqsUpTo(a, S, N);
  InSeqsUpTo(b, S, N);
}

method Solve(n: int, list1: seq<int>, list2: seq<int>) returns (output: string)
{
  var a := list1;
  var b := list2;
  var mark: set<(seq<int>, seq<int>)> := {};
  var ans := 0;
  var out := "";
  var found := false;
  ghost var S := set x | x in list1 + list2;
  ghost var N := |list1| + |list2|;
  ghost var U := States(S, N);
  while |a| > 0 && |b| > 0 && !found
    invariant |a| + |b| == N
    invariant forall x :: x in a ==> x in S
    invariant forall x :: x in b ==> x in S
    invariant mark <= U
    decreases (if found then 0 else 1), |U - mark|
  {
    if (a, b) in mark {
      out := "-1";
      found := true;
    } else {
      InStates(a, b, S, N);
      assert U - (mark + {(a, b)}) == (U - mark) - {(a, b)};
      mark := mark + {(a, b)};
      ans := ans + 1;
      var aa := a[0];
      var bb := b[0];
      a := a[1..];
      b := b[1..];
      if aa > bb {
        a := a + [bb, aa];
      } else {
        b := b + [aa, bb];
      }
    }
  }
  if !found {
    if |a| > 0 {
      out := JoinInts([ans, 1], " ");
    } else {
      out := JoinInts([ans, 2], " ");
    }
  }
  output := out;
}
