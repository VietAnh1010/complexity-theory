// --- Python ---------------------------------------------------------
// k = int(input().split()[1])
// result = {}
// prev = 0
// value = 0
// STR = input() + '$'
// 
// for letter in STR:
//     if letter != prev:
//         result[prev] = result.get(prev, 0) + value//k
//         prev = letter
//         value = 0
//     value+=1
// 
// print(max(result.values()))  
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(a: int, b: int, string_: string)
    returns (output: string, ghost steps: nat)
  requires b >= 1
  requires |string_| >= 1 ==> string_[0] != '\0'
  ensures steps <= 13 * ((|string_| + 1) * (|string_| + 1)) + 40 * (|string_| + 1) + 10 + |output|
{
  steps := 0;
  var k := b;
  steps := steps + |"$"|;
  var strSeq := string_ + "$";
  var entries: seq<(char, int)> := [];
  var prev := '\0';
  var value := 0;
  var i := 0;
  while i < |strSeq|
    invariant 0 <= i <= |strSeq|
    invariant |strSeq| == |string_| + 1
    invariant strSeq[0] != '\0'
    invariant i == 0 ==> prev == '\0'
    invariant i >= 1 ==> |entries| >= 1
    invariant |entries| <= i
    invariant steps <= 1 + 20 * i + 13 * (i * i)
    decreases |strSeq| - i
  {
    steps := steps + 3;
    steps := steps + 1;
    var letter := strSeq[i];
    assert i == 0 ==> letter != prev;
    steps := steps + 1;
    if letter != prev {
      steps := steps + 1;
      var addition := FloorDiv(value, k);
      var found := false;
      var newEntries: seq<(char, int)> := [];
      ghost var s0 := steps;
      var j := 0;
      while j < |entries|
        invariant 0 <= j <= |entries|
        invariant |newEntries| == j
        invariant found ==> j >= 1
        invariant steps <= s0 + 13 * j
        decreases |entries| - j
      {
        steps := steps + 3;
        steps := steps + 3;
        if entries[j].0 == prev {
          steps := steps + (5 + |[(prev, entries[j].1 + addition)]|);
          newEntries := newEntries + [(prev, entries[j].1 + addition)];
          found := true;
        } else {
          steps := steps + (2 + |[entries[j]]|);
          newEntries := newEntries + [entries[j]];
        }
        steps := steps + 1;
        j := j + 1;
      }
      steps := steps + 2;
      steps := steps + 1;
      if !found {
        steps := steps + (2 + |[(prev, addition)]|);
        newEntries := newEntries + [(prev, addition)];
      }
      assert |newEntries| >= 1;
      entries := newEntries;
      prev := letter;
      value := 0;
    }
    steps := steps + 1;
    value := value + 1;
    steps := steps + 1;
    SqStep(i);
    i := i + 1;
  }
  steps := steps + 2;
  var vals: seq<int> := [];
  ghost var s1 := steps;
  var j2 := 0;
  while j2 < |entries|
    invariant 0 <= j2 <= |entries|
    invariant |vals| == j2
    invariant steps <= s1 + 8 * j2
    decreases |entries| - j2
  {
    steps := steps + 3;
    steps := steps + (3 + |[entries[j2].1]|);
    vals := vals + [entries[j2].1];
    steps := steps + 1;
    j2 := j2 + 1;
  }
  steps := steps + 2;
  steps := steps + (|vals| + Digits(MaxSeq(vals)));
  output := IntToString(MaxSeq(vals));
  IntToStringDigits(MaxSeq(vals));
}

import opened Prelude

lemma SqStep(i: nat)
  ensures (i + 1) * (i + 1) == i * i + 2 * i + 1
{
}
