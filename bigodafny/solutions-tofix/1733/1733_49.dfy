// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : low
//   auditor        : labelaudit-batch-11
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     Python rebuilds the whole list c and calls c.index(i+1) once per
//     outer iteration of the n-step for loop, each O(n), giving Python
//     O(n**2) rather than the labelled O(n); the Dafny additionally builds
//     RepeatInt and ReverseInt via seq-concatenation at every recursive
//     level, the same shape the audit notes made 888_6's ReverseSeq
//     quadratic per call, so the true Dafny cost looks worse still,
//     plausibly cubic.
//
//   how this label could be wrong, and what to check:
//     The label claims O(n) but c.index(i+1) and the list rebuild
//     c=c[:i]+c[j:i-1:-1]+c[j+1:] each cost O(n) and run once per outer
//     iteration, so check whether Python is actually O(n**2); separately
//     confirm whether ReverseInt's `ReverseInt(s[1..]) + [s[0]]` recursion
//     is the same concatenate-at-every-level shape flagged as quadratic
//     for 888_6 -- if so, RepeatInt and ReverseInt called on segments up
//     to size n inside the O(n) outer loop push the Dafny past O(n**2).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 147, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "JoinInts"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 6,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1427_D. Unshuffling a Deck  (problem 1733, solution 1733_49)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// c=[*map(int,input().split())]
// if n%2:c=[n+1-i for i in c]
// q=0
// o=[]
// for i in range(n):
//     j=c.index(i+1)
//     m=[1]*i
//     if j-i+1:m.append(j-i+1)
//     m+=[1]*(n-1-j)
//     if i:c=c[:i]+c[j:i-1:-1]+c[j+1:]
//     else:c=c[:i]+c[j::-1]+c[j+1:]
//     if len(m)>1:
//         q+=1
//         if i%2:m=m[::-1]
//         m=[len(m)]+m
//         o.append(' '.join(map(str,m)))
// print(q)
// print('\n'.join(o))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function RepeatInt(v: int, cnt: int): seq<int>
  requires cnt >= 0
  ensures |RepeatInt(v, cnt)| == cnt
  decreases cnt
{
  if cnt == 0 then [] else [v] + RepeatInt(v, cnt - 1)
}

function ReverseInt(s: seq<int>): seq<int>
  ensures |ReverseInt(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseInt(s[1..]) + [s[0]]
}

function IndexOfInt(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == v then 0
  else 1 + IndexOfInt(s[1..], v)
}

lemma IndexOfFindsLeftmost(s: seq<int>, v: int)
  requires v in s
  ensures 0 <= IndexOfInt(s, v) < |s|
  ensures s[IndexOfInt(s, v)] == v
  ensures forall t :: 0 <= t < IndexOfInt(s, v) ==> s[t] != v
  decreases |s|
{
  if s[0] == v {
  } else {
    IndexOfFindsLeftmost(s[1..], v);
  }
}

lemma ReverseIntElems(s: seq<int>)
  ensures forall t :: 0 <= t < |s| ==> ReverseInt(s)[t] == s[|s| - 1 - t]
  decreases |s|
{
  if |s| == 0 {
  } else {
    ReverseIntElems(s[1..]);
  }
}

lemma ReverseIntMembership(s: seq<int>)
  ensures forall v :: v in ReverseInt(s) <==> v in s
  decreases |s|
{
  if |s| == 0 {
  } else {
    ReverseIntMembership(s[1..]);
  }
}

method Solve(a: int, b_list: seq<int>) returns (output: string)
  requires |b_list| == a
  requires forall v :: 1 <= v <= a ==> v in b_list
{
  var n := a;
  var c: seq<int> := b_list;
  if n % 2 == 1 {
    var cOld0 := c;
    var nc: seq<int> := [];
    var k := 0;
    while k < |c|
      invariant 0 <= k <= |c|
      invariant |nc| == k
      invariant forall t :: 0 <= t < k ==> nc[t] == n + 1 - cOld0[t]
      decreases |c| - k
    {
      nc := nc + [n + 1 - c[k]];
      k := k + 1;
    }
    c := nc;
    assert forall v :: 1 <= v <= n ==> v in c by {
      forall v | 1 <= v <= n
        ensures v in c
      {
        assert 1 <= n + 1 - v <= n;
        assert n + 1 - v in cOld0;
        IndexOfFindsLeftmost(cOld0, n + 1 - v);
        var idx := IndexOfInt(cOld0, n + 1 - v);
        assert 0 <= idx < |cOld0| && cOld0[idx] == n + 1 - v;
        assert c[idx] == n + 1 - cOld0[idx];
        assert c[idx] == v;
      }
    }
  }
  var q := 0;
  var o: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |c| == n
    invariant forall t :: 0 <= t < i ==> c[t] == t + 1
    invariant forall v :: 1 <= v <= n ==> v in c
    decreases n - i
  {
    assert i + 1 in c by {
      assert 1 <= i + 1 <= n;
    }
    IndexOfFindsLeftmost(c, i + 1);
    var j := IndexOfInt(c, i + 1);
    assert i <= j;
    var m: seq<int> := RepeatInt(1, i);
    if j - i + 1 != 0 {
      m := m + [j - i + 1];
    }
    var tail := n - 1 - j;
    var tailN := if tail < 0 then 0 else tail;
    m := m + RepeatInt(1, tailN);
    var seg := c[i..j + 1];
    var mid := ReverseInt(seg);
    ReverseIntElems(seg);
    ReverseIntMembership(seg);
    assert mid[0] == c[j];
    var cOld := c;
    c := c[..i] + mid + c[j + 1..];
    assert c[i] == i + 1 by {
      assert (mid + cOld[j + 1..])[0] == mid[0];
    }
    assert forall t :: 0 <= t < i ==> c[t] == t + 1 by {
      assert c[..i] == cOld[..i];
    }
    assert forall v :: 1 <= v <= n ==> v in c by {
      forall v | 1 <= v <= n
        ensures v in c
      {
        assert v in cOld;
        assert cOld == cOld[..i] + seg + cOld[j + 1..];
        if v in cOld[..i] {
        } else if v in seg {
          assert v in mid;
        } else {
        }
      }
    }
    if |m| > 1 {
      q := q + 1;
      if i % 2 == 1 {
        m := ReverseInt(m);
      }
      m := [|m|] + m;
      o := o + [JoinInts(m, " ")];
    }
    i := i + 1;
  }
  output := IntToString(q) + "\n" + Join(o, "\n");
}
