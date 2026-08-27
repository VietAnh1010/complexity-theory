(** Merge sort on singly-linked lists, in HeapLang.

    Lists follow the representation used by [iris_time.Examples]:
    the empty list is [NONEV], and a cons cell is [SOMEV #p] where
    [p ↦ (#x, tail)]. *)

From iris_time.heap_lang Require Import notation.

(** [split_list l] deals the elements of [l] out into two fresh lists,
    taking every other element.  It allocates; the input list is left
    untouched (and simply dropped by the caller). *)
Definition split_list : val :=
  rec: "split" "l" :=
    match: "l" with
      NONE => (NONE, NONE)
    | SOME "p" =>
      let: "x" := Fst !"p" in
      let: "t" := Snd !"p" in
      match: "t" with
        NONE => (SOME (ref ("x", NONE)), NONE)
      | SOME "q" =>
        let: "y" := Fst !"q" in
        let: "t2" := Snd !"q" in
        let: "r" := "split" "t2" in
        (SOME (ref ("x", Fst "r")), SOME (ref ("y", Snd "r")))
      end
    end.

(** [merge_list l1 l2] merges two sorted lists into a fresh sorted list.
    The recursion pattern matches stdpp's [list_merge] exactly. *)
Definition merge_list : val :=
  rec: "merge" "l1" "l2" :=
    match: "l1" with
      NONE => "l2"
    | SOME "p" =>
      match: "l2" with
        NONE => SOME "p"
      | SOME "q" =>
        let: "x" := Fst !"p" in
        let: "t1" := Snd !"p" in
        let: "y" := Fst !"q" in
        let: "t2" := Snd !"q" in
        if: "x" ≤ "y" then
          SOME (ref ("x", "merge" "t1" (SOME "q")))
        else
          SOME (ref ("y", "merge" (SOME "p") "t2"))
      end
    end.

(** Top-down merge sort. *)
Definition msort : val :=
  rec: "msort" "l" :=
    match: "l" with
      NONE => NONE
    | SOME "p" =>
      let: "t" := Snd !"p" in
      match: "t" with
        NONE => SOME "p"
      | SOME "q" =>
        let: "r" := split_list (SOME "p") in
        merge_list ("msort" (Fst "r")) ("msort" (Snd "r"))
      end
    end.
