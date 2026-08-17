(** * Catalog.v — the index from BigO(Bench) samples to proved bounds.

    This file is an INDEX, not evidence. The [proved] field is a string: Coq
    does not check that it describes the theorem in the corresponding example
    file. The evidence is the theorem, and the only thing keeping the two in
    sync is that [make check] fails if any proof is admitted, plus review.

    Do not let this table grow a claim that no example file backs. If an entry
    has no [Theorem] behind it, it does not belong here. *)

From Coq Require Import String List.
Import ListNotations.
Open Scope string_scope.

(** How the proved bound relates to the label BigO(Bench)'s framework fitted. *)
Inductive verdict :=
  (** The fitted label is exactly the proved growth rate. *)
  | Tight
  (** A matching upper bound is proved, but no matching lower bound, so
      tightness is open. Distinct from [Tight]: claiming tightness would
      require a lower bound that is sometimes false of the real program —
      Python's Timsort is linear on sorted input where merge sort is not. *)
  | SoundUpperOnly
  (** The fitted label is a correct upper bound but not the tight one, or it
      names size parameters the program does not actually depend on. *)
  | SoundLoose
  (** The program is asymptotically CHEAPER than the label claims. The label
      still upper-bounds the cost, so this is a precision failure, not a
      correctness one — but it is a large one. *)
  | UnsoundOver
  (** The program is asymptotically MORE EXPENSIVE than the label claims. The
      label is not an upper bound at all. *)
  | UnsoundUnder.

Record entry := {
  solution_id  : string;
  problem_name : string;
  fitted_label : string;   (* verbatim from time_complexity_inferred *)
  size_param   : string;   (* what "n" is taken to mean in this file *)
  proved_bound : string;   (* informal restatement of the example's theorem *)
  theorem_name : string;   (* the qualified name that backs this row *)
  v            : verdict
}.

Definition catalog : list entry := [
  {| solution_id  := "2389_139";
     problem_name := "p04012 AtCoder Beginner Contest 044 - Beautiful Strings";
     fitted_label := "O(n**2)";
     size_param   := "length of the input string";
     proved_bound := "cost = n * n exactly";
     theorem_name := "S2389_139.fitted_label_is_tight";
     v            := Tight |} ;

  {| solution_id  := "603_284";
     problem_name := "1041_A. Heist";
     fitted_label := "O(nlogn)";
     size_param   := "N, the length of the list read";
     proved_bound := "cost <= 2n*log2_up(n) + 2n, and cost >= n; gap open";
     theorem_name := "S603_284.fitted_label_sound";
     v            := SoundUpperOnly |} ;

  {| solution_id  := "1421_53";
     problem_name := "p02899 AtCoder Beginner Contest 142 - Go to School";
     fitted_label := "O(n+m)";
     size_param   := "N, which is also the length of A";
     proved_bound := "cost = 2n; the label's second parameter is spurious";
     theorem_name := "S1421_53.fitted_label_sound";
     v            := SoundLoose |} ;

  {| solution_id  := "450_204";
     problem_name := "1421_C. Palindromifier";
     fitted_label := "O(1)";
     size_param   := "length of the single input line";
     proved_bound := "cost = n; not O(1)";
     theorem_name := "S450_204.fitted_label_unsound";
     v            := UnsoundUnder |} ;

  {| solution_id  := "5_100";
     problem_name := "622_A. Infinite Sequence";
     fitted_label := "O(n)";
     size_param   := "the numeric VALUE of the input integer";
     proved_bound := "cost*(cost+1) <= 2n, i.e. ~sqrt(2n); not Omega(n)";
     theorem_name := "S5_100.fitted_label_not_tight";
     v            := UnsoundOver |}
].
