// 1283_C. Friends and Gifts  (problem 1336, solution 1336_157)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// f = [int(i) for i in input().split()]
// s = set([i for i in range(1, n + 1)])
// zero = [i for i, a in enumerate(f) if a == 0]
// x = list(s - set(f))
// for a, b in zip(zero, x):
//     f[a] = b
// for i in range(len(zero) - 1):
//     a = zero[i]
//     if f[a] == a + 1:
//         f[a] = f[zero[i + 1]]
//         f[zero[i + 1]] = a + 1
// a = zero[-1]
// if f[a] == a + 1:
//     f[a] = f[zero[0]]
//     f[zero[0]] = a + 1
// print(*f)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ZeroIndicesFrom(f: seq<int>, i: int): seq<int>
  requires 0 <= i <= |f|
  decreases |f| - i
{
  if i == |f| then []
  else if f[i] == 0 then [i] + ZeroIndicesFrom(f, i + 1)
  else ZeroIndicesFrom(f, i + 1)
}

function ZeroIndices(f: seq<int>): seq<int>
{
  ZeroIndicesFrom(f, 0)
}

// Python's `list(s - set(f))` does NOT come out in ascending order: for a
// small result set, CPython's set table stays at its minimum size (8 slots),
// so values wrap modulo the table size and the iteration order depends on
// CPython's actual open-addressing insert. Reproducing "ascending order"
// here would be a different (wrong) answer, not a tidier one -- so this
// simulates CPython's set insertion (hash(int) == int, linear probing with
// 9-step runs between perturbation jumps, PySet_MINSIZE == 8) exactly.
method ProbeInsert(table: seq<int>, mask: int, key: int) returns (table2: seq<int>, inserted: bool)
  requires |table| == mask + 1
  requires key >= 0
  ensures |table2| == mask + 1
  decreases *
{
  var perturb := key;
  var i := BitAnd(key, mask);
  var tbl := table;
  var done := false;
  inserted := false;
  while !done
    invariant |tbl| == mask + 1
    decreases *
  {
    var probes := if i + 9 <= mask then 9 else 0;
    var j := i;
    var steps := 0;
    var slot := -1;
    var dup := false;
    while steps <= probes && slot == -1 && !dup
      invariant 0 <= j < mask + 1 || steps > probes
      decreases probes - steps + 1
    {
      if tbl[j] == -1 {
        slot := j;
      } else if tbl[j] == key {
        dup := true;
      } else {
        j := j + 1;
        steps := steps + 1;
      }
    }
    if slot != -1 {
      tbl := tbl[slot := key];
      inserted := true;
      done := true;
    } else if dup {
      inserted := false;
      done := true;
    } else {
      perturb := perturb / 32;
      i := BitAnd(i * 5 + 1 + perturb, mask);
    }
  }
  table2 := tbl;
}

method InsertWithResize(table: seq<int>, mask: int, used: int, key: int) returns (table2: seq<int>, mask2: int, used2: int)
  requires |table| == mask + 1
  requires key >= 0
  requires used >= 0
  ensures |table2| == mask2 + 1
  decreases *
{
  var t1, ins := ProbeInsert(table, mask, key);
  if !ins {
    table2 := t1;
    mask2 := mask;
    used2 := used;
    return;
  }
  var newUsed := used + 1;
  if newUsed * 5 < mask * 3 {
    table2 := t1;
    mask2 := mask;
    used2 := newUsed;
  } else {
    var minused := if newUsed <= 50000 then newUsed * 4 else newUsed * 2;
    var newsize := 8;
    while newsize <= minused
      decreases minused - newsize + 1
    {
      newsize := newsize * 2;
    }
    var newmask := newsize - 1;
    var newtable: seq<int> := seq(newsize, _ => -1);
    var p := 0;
    while p < |t1|
      invariant 0 <= p <= |t1|
      invariant |newtable| == newsize
      decreases |t1| - p
    {
      if t1[p] != -1 {
        var nt, _ := ProbeInsert(newtable, newmask, t1[p]);
        newtable := nt;
      }
      p := p + 1;
    }
    table2 := newtable;
    mask2 := newmask;
    used2 := newUsed;
  }
}

method BuildMissingSet(f: seq<int>, N: int) returns (result: seq<int>)
  requires N >= 0
  decreases *
{
  var sortedF := SortInts(f);
  var table: seq<int> := seq(8, _ => -1);
  var mask := 7;
  var used := 0;
  var v := 1;
  var fj := 0;
  while v <= N
    invariant 1 <= v
    invariant 0 <= fj <= |sortedF|
    invariant |table| == mask + 1
    decreases N - v
  {
    while fj < |sortedF| && sortedF[fj] < v
      decreases |sortedF| - fj
    {
      fj := fj + 1;
    }
    if fj >= |sortedF| || sortedF[fj] != v {
      var t2, m2, u2 := InsertWithResize(table, mask, used, v);
      table := t2;
      mask := m2;
      used := u2;
    }
    v := v + 1;
  }
  result := [];
  var idx := 0;
  while idx < |table|
    invariant 0 <= idx <= |table|
    decreases |table| - idx
  {
    if table[idx] != -1 {
      result := result + [table[idx]];
    }
    idx := idx + 1;
  }
}

method Solve(N: int, tree_heights: seq<int>) returns (output: string)
  requires N == |tree_heights|
  decreases *
{
  var f := tree_heights;
  var zero := ZeroIndices(f);
  var missing := BuildMissingSet(f, N);
  var i := 0;
  var mlen := if |zero| < |missing| then |zero| else |missing|;
  while i < mlen
    invariant 0 <= i <= mlen
    decreases mlen - i
  {
    f := f[zero[i] := missing[i]];
    i := i + 1;
  }
  var j := 0;
  while j < |zero| - 1
    invariant 0 <= j <= |zero|
    decreases |zero| - j
  {
    var a := zero[j];
    if f[a] == a + 1 {
      var b := zero[j + 1];
      f := f[a := f[b]];
      f := f[b := a + 1];
    }
    j := j + 1;
  }
  if |zero| > 0 {
    var a := zero[|zero| - 1];
    if f[a] == a + 1 {
      var b := zero[0];
      f := f[a := f[b]];
      f := f[b := a + 1];
    }
  }
  output := JoinInts(f, " ") + "\n";
}
