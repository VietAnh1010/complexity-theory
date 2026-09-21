// GATE INAPPLICABLE -- `validate.py` cannot reach a verdict on this row.
//
//   tests stored    : 12
//   runnable        : 10   (Dafny passes all 10)
//   unparseable     : 2    the problem's own Input.from_str raises on them
//   cause           : 2 stored tests declare n = 4 and supply 3 text lines, so
//                     `assert len(text_list) == n` fails before either the
//                     Python or the Dafny is run
//   control         : batches/gate-audit/control.py, 2026-09-21 -- the original
//                     Python through the same dataclass round-trip also passes
//                     10 and cannot run the other 2
//   record          : data/gate_ungateable.jsonl
//   filed           : solutions-ungateable/, 2026-09-21
//
// 53_A. Autocomplete  (problem 1196, solution 1196_100)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// target = input()
// count = input()
// srchlist = []
// for i in range(0,int(count)):
//     srch = input()
//     srchlist.append(srch)
// srchlist.sort()
// final = target
// for item in srchlist:
//     if item.find(target) == 0:
//         final = item
//         break
// print(final)
// 	 			 					  	 	    		 		  		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string, n: int, text_list: seq<string>) returns (output: string)
{
  var sorted_list := Sort(text_list, StringLess);
  var final_ans := text;
  var i := 0;
  var found := false;
  while i < |sorted_list| && !found
    decreases |sorted_list| - i
  {
    var item := sorted_list[i];
    if |item| >= |text| && item[..|text|] == text {
      final_ans := item;
      found := true;
    }
    i := i + 1;
  }
  output := final_ans;
}

function StringLess(a: string, b: string): bool
{
  if |a| == 0 then |b| > 0
  else if |b| == 0 then false
  else if a[0] != b[0] then a[0] < b[0]
  else StringLess(a[1..], b[1..])
}
