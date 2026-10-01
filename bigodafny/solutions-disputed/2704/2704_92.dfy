// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-s04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve pays O(n**2) for the dedupe scan over result plus O(m**2) per
//     word for the repeated ReplaceAll fixpoint in Reduce, for O(n**2 +
//     n*m**2) over n words of length m; the Python's recursive replacement
//     with str.replace pays the same, so the label omits a size both
//     programs pay for.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) names only the word count n. Check Reduce: it
//     repeats ReplaceAll (linear in the word length m) until a fixpoint,
//     up to O(m) rounds, so each word costs O(m**2) on top of the O(n)
//     dedupe scan over result. If you decide the 20-char word cap makes m
//     negligible, the label stands as O(n**2); the rule says caps do not
//     make a size constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 49, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString", "ReplaceAll"],
//     "loop_depth": 2, "loops": 3, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": true, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 883_F. Lost in Transliteration  (problem 2704, solution 2704_92)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def replacement(str):
// 	str2 = str.replace("oo","u")
// 	str3 = str2.replace("kh","h")
// 	if str3 == str:
// 		return str3
// 	else :
// 		str3 = replacement(str3)
// 		return str3
// 	
// 	
// 
// 
// n = int(input())
// myList = []
// myList2 = []
// for i in range(n):
// 	myList.append(input())
// for x in myList:
// 	
// 	str4 = replacement(x)
// 	str4 = str4.replace("u","oo")
// 	str4 = str4.replace("h","kh")
// 	
// 	exist = False
// 	for str in myList2:
// 		if str4 == str:
// 			exist = True
// 	if exist == False:
// 		myList2.append(str4)
// 
// print(len(myList2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Reduce(s0: string) returns (result: string)
  decreases *
{
  var s := s0;
  var changed := true;
  while changed
    decreases *
  {
    var s2 := ReplaceAll(s, "oo", "u");
    var s3 := ReplaceAll(s2, "kh", "h");
    if s3 == s {
      changed := false;
    } else {
      s := s3;
    }
  }
  result := s;
}

method Solve(n: int, names: seq<string>) returns (output: string)
  requires n == |names|
  decreases *
{
  var result: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var str4 := Reduce(names[i]);
    str4 := ReplaceAll(str4, "u", "oo");
    str4 := ReplaceAll(str4, "h", "kh");
    var exists_ := false;
    var j := 0;
    while j < |result|
      invariant 0 <= j <= |result|
      decreases |result| - j
    {
      if result[j] == str4 { exists_ := true; }
      j := j + 1;
    }
    if !exists_ {
      result := result + [str4];
    }
    i := i + 1;
  }
  output := IntToString(|result|);
}
