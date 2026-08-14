(** * S450_204 — verdict: UNSOUND_UNDER (the program is more expensive than
      the fitted label says)

    BigO(Bench) time_complexity_test_set
      solution_id   450_204
      problem_name  1421_C. Palindromifier
      fitted label  O(1)

    Source solution, verbatim:

      print('3 L 2 R 2 R',len(input())*2-1)

    COST MODEL. [len] on an existing Python [str] is O(1) and is charged
    nothing. But [input()] must read the line, and that is linear in the
    line's length — one tick per character consumed. Nothing else in the
    program depends on the input.

    So the total cost is exactly the input length, and the fitted O(1) is
    wrong: it is not a loose bound, it is not an upper bound at all. The
    likely cause is that the framework's input expansion did not scale the
    single line this problem reads, so runtime looked flat.

    This is the failure mode worth cataloguing: a label that is unsound rather
    than imprecise. Note it is still consistent with the paper's own framing —
    labels are fitted performance profiles, not theorems. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(** [input()] — consumes the line, returning its length. *)
Fixpoint read_line (s : list nat) : M nat :=
  match s with
  | [] => ret 0
  | _ :: r => tick (n <- read_line r ;; ret (S n))
  end.

Lemma cost_read_line : forall s, cost (read_line s) = length s.
Proof.
  intros s. induction s as [| x r IH]; [reflexivity|].
  simpl read_line. rewrite cost_tick, cost_bind, IH. simpl. lia.
Qed.

Definition palindromifier (s : list nat) : M nat :=
  n <- read_line s ;; ret (2 * n - 1).

Theorem cost_palindromifier : forall s,
    cost (palindromifier s) = length s.
Proof.
  intros s. unfold palindromifier. rewrite cost_bind, cost_read_line.
  simpl. lia.
Qed.

Definition T (n : nat) : nat := cost (palindromifier (List.seq 0 n)).

Lemma T_eq : forall n, T n = n.
Proof.
  intros n. unfold T. rewrite cost_palindromifier, List.seq_length.
  reflexivity.
Qed.

(** ** The disagreement, as a theorem. *)

Theorem fitted_label_unsound : ~ BigO T (fun _ => 1).
Proof.
  apply not_BigO. intros c n0.
  exists (S (Nat.max c n0)). split.
  - pose proof (Nat.le_max_r c n0). lia.
  - rewrite T_eq. pose proof (Nat.le_max_l c n0). lia.
Qed.

(** And the true class, for the catalog. *)
Theorem true_class : Theta T (fun n => n).
Proof.
  split; [exists 1, 0 | exists 1, 0]; intros n _; rewrite T_eq; lia.
Qed.
