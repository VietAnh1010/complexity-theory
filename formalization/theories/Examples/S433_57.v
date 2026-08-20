(** * S433_57 — verdict: TIGHT

    BigO(Bench) time_complexity_test_set
      solution_id   433_57
      problem_name  257_B. Playing Cubes
      fitted label  O(1)

    Source, verbatim:

      f=input().split()
      kras=int(f[0])
      sin=int(f[1])
      print(max(kras,sin)-1,min(kras,sin))

    COST MODEL. Reading and parsing the line and printing the result are free,
    per the convention in [Cost.v]. Indexing a Python list is O(1). What
    remains is three elementary operations — [max], [min], and the [-1] — so
    the cost is 3 on every input.

    WHAT "n" IS. The length of the input line. The cost does not depend on it:
    [cost_is_constant] below is equality on any two inputs, not a bound on a
    chosen family.

    The only input-dependent step is reading stdin, which is free, so the
    fitted O(1) is correct. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** [f=input().split()] then [int(f[0])], [int(f[1])] — parsing, charged
    nothing. [f] arrives as the list of parsed fields. *)
Definition solve (f : list nat) : M (nat * nat) :=
  let a := nth 0 f 0 in
  let b := nth 1 f 0 in
  charge 3 (ret (Nat.max a b - 1, Nat.min a b)).

Theorem cost_solve : forall f, cost (solve f) = 3.
Proof. intros f. reflexivity. Qed.

(** The strong form of O(1): not merely bounded, but the same number on any
    two inputs. No size-indexed family is involved. *)
Theorem cost_is_constant : forall f g, cost (solve f) = cost (solve g).
Proof. intros f g. reflexivity. Qed.

Definition T (n : nat) : nat := cost (solve (List.seq 0 n)).

Lemma T_eq : forall n, T n = 3.
Proof. intros n. reflexivity. Qed.

(** ** The fitted label is tight. *)
Theorem fitted_label_is_tight : Theta T (fun _ => 1).
Proof.
  split; [exists 3, 0 | exists 1, 0]; intros n _; rewrite T_eq; lia.
Qed.
