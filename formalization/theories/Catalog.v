(** * Catalog.v — index from BigO(Bench) samples to proved bounds.

    An INDEX, not evidence. [proved_bound] is a string; Rocq does not check it
    against the theorem named in [theorem_name]. The evidence is the theorem.
    Keeping the two in sync rests on [make check] failing on any admitted
    proof, plus review. Do not add a row that no example file backs.

    WITHDRAWN: 450_204, formerly the set's only [NotUpperBound]. Its verdict
    came from charging [input()] per character, which makes any program that
    reads its input Omega(input size). Under [Cost.v]'s convention — input and
    output are free — the fitted O(1) is correct. [Examples/S450_204.v] is kept
    and still compiles; it has no row here. *)

From Stdlib Require Import String List.
Import ListNotations.
Open Scope string_scope.

(** How the proved bound relates to the label the framework fitted. *)
Inductive verdict :=
  (** Label is exactly the proved growth rate. *)
  | Tight
  (** Matching upper bound proved, no matching lower bound, so tightness is
      open. Distinct from [Tight]: [Tight] would need a lower bound that is
      sometimes false of the real program — Python's Timsort is linear on
      sorted input where merge sort is not. *)
  | SoundUpperOnly
  (** Correct upper bound but not the tight one, or names size parameters the
      program does not depend on. *)
  | SoundLoose
  (** Program is asymptotically CHEAPER than the label. The label still upper
      bounds the cost, so this is a precision failure, not a correctness one. *)
  | Overstated
  (** Program is asymptotically MORE EXPENSIVE than the label. The label is not
      an upper bound at all. No row currently uses this: the one entry that
      did, 450_204, was withdrawn (see the header). *)
  | NotUpperBound.

Record entry := {
  solution_id  : string;
  problem_name : string;
  fitted_label : string;   (* verbatim from time_complexity_inferred *)
  size_param   : string;   (* what "n" means in this file *)
  proved_bound : string;   (* informal restatement of the theorem *)
  source_file  : string;   (* where the proof lives *)
  theorem_name : string;   (* the theorem backing this row *)
  v            : verdict
}.

Definition catalog : list entry := [
  {| solution_id  := "2389_139";
     problem_name := "p04012 AtCoder Beginner Contest 044 - Beautiful Strings";
     fitted_label := "O(n**2)";
     size_param   := "length of the input string";
     proved_bound := "cost = n * n exactly";
     source_file  := "theories/Examples/S2389_139.v";
     theorem_name := "S2389_139.fitted_label_is_tight";
     v            := Tight |} ;

  {| solution_id  := "167_177";
     problem_name := "1184_A1. Heidi Learns Hashing (Easy)";
     fitted_label := "O(n)";
     size_param   := "the numeric VALUE of the input integer";
     proved_bound := "cost <= sqrt(n); not Omega(n)";
     source_file  := "theories/Examples/S167_177.v";
     theorem_name := "S167_177.fitted_label_not_tight";
     v            := Overstated |} ;

  {| solution_id  := "603_284";
     problem_name := "1041_A. Heist";
     fitted_label := "O(nlogn)";
     size_param   := "N, the length of the list read";
     proved_bound := "n <= cost <= 2n*log2_up(n) + 2n; gap left open";
     source_file  := "theories/Examples/S603_284.v";
     theorem_name := "S603_284.fitted_label_sound";
     v            := SoundUpperOnly |} ;

  {| solution_id  := "1421_53";
     problem_name := "p02899 AtCoder Beginner Contest 142 - Go to School";
     fitted_label := "O(n+m)";
     size_param   := "N, which is also the length of A";
     proved_bound := "cost = n; the label names a second parameter unused";
     source_file  := "theories/Examples/S1421_53.v";
     theorem_name := "S1421_53.fitted_label_sound";
     v            := SoundLoose |} ;

  (* Replaces the withdrawn 450_204. *)
  {| solution_id  := "433_57";
     problem_name := "257_B. Playing Cubes";
     fitted_label := "O(1)";
     size_param   := "length of the input line";
     proved_bound := "cost = 3 on every input";
     source_file  := "theories/Examples/S433_57.v";
     theorem_name := "S433_57.fitted_label_is_tight";
     v            := Tight |} ;

  {| solution_id  := "5_100";
     problem_name := "622_A. Infinite Sequence";
     fitted_label := "O(n)";
     size_param   := "the numeric VALUE of the input integer";
     proved_bound := "Theta(sqrt n): cost*(cost+1) <= 2n, cost >= sqrt(n)-2; not Omega(n)";
     source_file  := "theories/Examples/S5_100.v";
     theorem_name := "S5_100.fitted_label_not_tight";
     v            := Overstated |}
].
